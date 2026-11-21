#!/usr/bin/env bash
# Encodes the synthetic images of scripts/make_images.py as lossy WebP with
# cwebp, cycling through six option sets so the corpus covers the loop
# filter types and strengths, segments, partition limits, sharp YUV, and the
# ALPH chunk's compression and filter methods.
#   scripts/make_lossy.sh CWEBP PAM_DIR OUT_DIR
set -euo pipefail
cw=$1; pam=$2; out=$3
mkdir -p "$out"
i=0
for p in "$pam"/*.pam; do
  b=$(basename "${p%.pam}")
  i=$((i + 1))
  case $((i % 6)) in
    0) o="-q 75" ;;
    1) o="-q 10 -f 0" ;;
    2) o="-q 95 -sharpness 7 -strong" ;;
    3) o="-q 50 -nostrong -f 100 -segments 1" ;;
    4) o="-q 30 -partition_limit 100 -alpha_filter best -alpha_method 0" ;;
    5) o="-q 85 -sns 100 -alpha_q 50 -sharp_yuv" ;;
  esac
  # shellcheck disable=SC2086
  "$cw" -quiet $o "$p" -o "$out/lossy_$b.webp"
done
