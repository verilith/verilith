#!/usr/bin/env bash
# Quiets a dedicated Linux machine for timing, and puts it back afterwards.
#
#   sudo bench/scripts/linux-quiet.sh on [CPU]   # default CPU: the last one
#   sudo bench/scripts/linux-quiet.sh off
#   bench/scripts/linux-quiet.sh status
#
# `on` turns off frequency boost (Intel turbo or the cpufreq `boost` knob),
# sets every core's governor to `performance`, takes CPU's hyperthread
# sibling offline so nothing shares its core, steers interrupts away from
# it, and allows perf counters without root (`perf_event_paranoid` 1). Then
# run the benchmark on that CPU:
#
#   VBENCH_CPU=CPU ./run.sh
#
# `off` restores every setting `on` changed, from the state file it wrote.
# Nothing here survives a reboot. On a shared cloud VM most of these knobs
# do not exist or do nothing; the script says which ones it could not set.
set -euo pipefail

STATE=/run/vbench-quiet.state
cmd=${1:-status}

need_root() {
    if [ "$(id -u)" != 0 ]; then
        echo "$0 $cmd: run as root (sudo)" >&2
        exit 1
    fi
}

# Writes VALUE to FILE, recording the old value so `off` can restore it.
set_knob() {
    local file=$1 value=$2
    if [ ! -w "$file" ]; then
        echo "  skip: $file (not present or not writable)"
        return
    fi
    local old
    old=$(cat "$file")
    if [ "$old" = "$value" ]; then
        echo "  ok:   $file = $value"
        return
    fi
    printf '%s\t%s\n' "$file" "$old" >> "$STATE"
    if echo "$value" > "$file" 2>/dev/null; then
        echo "  set:  $file = $value (was $old)"
    else
        echo "  fail: $file = $value"
    fi
}

status() {
    show() { [ -r "$1" ] && printf '  %-60s %s\n' "$1" "$(cat "$1")"; return 0; }
    show /sys/devices/system/cpu/intel_pstate/no_turbo
    show /sys/devices/system/cpu/cpufreq/boost
    show /proc/sys/kernel/perf_event_paranoid
    show /proc/sys/kernel/randomize_va_space
    if ls /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor >/dev/null 2>&1; then
        echo "  governors:$(cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | sort | uniq -c | tr -s ' ' | tr '\n' ' ')"
    fi
    echo "  online CPUs: $(cat /sys/devices/system/cpu/online)"
    if command -v systemctl >/dev/null; then
        echo "  irqbalance: $(systemctl is-active irqbalance 2>/dev/null || true)"
    fi
    if grep -q hypervisor /proc/cpuinfo; then
        echo "  note: this is a virtual machine; timings share the host with other tenants"
    fi
    [ -f "$STATE" ] && echo "  quiet mode is on (state in $STATE)"
    return 0
}

case "$cmd" in
on)
    need_root
    if [ -f "$STATE" ]; then
        echo "already on (state in $STATE); run '$0 off' first" >&2
        exit 1
    fi
    cpu=${2:-$(($(nproc --all) - 1))}
    if [ ! -d "/sys/devices/system/cpu/cpu$cpu" ]; then
        echo "no CPU $cpu (CPUs: $(cat /sys/devices/system/cpu/possible))" >&2
        exit 2
    fi
    : > "$STATE"
    echo "quieting the machine for CPU $cpu"
    set_knob /sys/devices/system/cpu/intel_pstate/no_turbo 1
    set_knob /sys/devices/system/cpu/cpufreq/boost 0
    for g in /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor; do
        [ -e "$g" ] && set_knob "$g" performance
    done
    set_knob /proc/sys/kernel/perf_event_paranoid 1
    # The other hyperthread on CPU's core, if any.
    sib=/sys/devices/system/cpu/cpu$cpu/topology/thread_siblings_list
    if [ -r "$sib" ]; then
        for s in $(tr ',' ' ' < "$sib" | sed 's/-/ /'); do
            [ "$s" != "$cpu" ] && set_knob "/sys/devices/system/cpu/cpu$s/online" 0
        done
    fi
    # Interrupts on every CPU but this one, where the kernel allows it.
    # irqbalance would move them back within seconds: stop it first.
    if command -v systemctl >/dev/null && systemctl is-active --quiet irqbalance 2>/dev/null; then
        systemctl stop irqbalance && printf 'service\tirqbalance\n' >> "$STATE" && echo "  set:  stopped irqbalance"
    fi
    # As a CPU list (smp_affinity_list): a hex smp_affinity mask must be
    # split by commas every 32 CPUs, and a 96-CPU machine needs that.
    last=$(($(nproc --all) - 1))
    others=""
    [ "$cpu" -gt 0 ] && others="0-$((cpu - 1))"
    [ "$cpu" -lt "$last" ] && others="${others:+$others,}$((cpu + 1))-$last"
    moved=0 kept=0
    for irq in /proc/irq/*/smp_affinity_list; do
        if echo "$others" > "$irq" 2>/dev/null; then moved=$((moved + 1)); else kept=$((kept + 1)); fi
    done
    echo "  set:  $moved interrupts steered to CPUs $others, $kept the kernel would not move (not restored by 'off')"
    echo
    echo "now: VBENCH_CPU=$cpu ./run.sh"
    echo "for the cleanest numbers also boot with isolcpus=$cpu nohz_full=$cpu, and stop"
    echo "cron, unattended upgrades and anything else that wakes up on a timer"
    ;;
off)
    need_root
    if [ ! -f "$STATE" ]; then
        echo "quiet mode is not on" >&2
        exit 0
    fi
    # Restore in reverse order, so CPUs come back online before anything else.
    tac "$STATE" | while IFS=$'\t' read -r file old; do
        if [ "$file" = service ]; then
            systemctl start "$old" && echo "  restored: started $old" || echo "  fail:     start $old"
            continue
        fi
        if echo "$old" > "$file" 2>/dev/null; then
            echo "  restored: $file = $old"
        else
            echo "  fail:     $file = $old"
        fi
    done
    rm -f "$STATE"
    ;;
status)
    status
    ;;
*)
    echo "usage: $0 on [CPU] | off | status" >&2
    exit 2
    ;;
esac
