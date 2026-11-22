//! Timing of the on-demand reader (`verilith_json::ondemand::Reader`) against the
//! tape API.
//!
//! `cargo run --release --example ondemand_bench -- DIR [SECONDS_PER_CASE]`
//! where DIR holds simdjson's twitter, citm_catalog, canada, mesh,
//! gsoc-2018 and github_events `.json`. For each access pattern it times,
//! interleaved, best of many runs:
//!
//! * `eager`, `lazy`: the tape API, a full parse and a read from the tape;
//! * `ondemand`: stage 1 and a read straight from its index. What is read
//!   is checked; what is skipped is only bracket-counted;
//! * `stage1`: stage 1 alone, the floor of `ondemand`.
//!
//! All three readers must return the same checksum. `simdjson_od.cpp` is
//! the same four patterns against simdjson's On Demand and DOM front ends.
mod cases;
mod od;
use cases::*;
use od::R;
use std::hint::black_box;
use std::time::Instant;
use verilith_json::ondemand::Reader;

struct Case {
    file: &'static str,
    name: &'static str,
    t: fn(verilith_json::Value) -> u64,
    o: for<'a> fn(&mut Reader<'a>, &mut Vec<u8>) -> R<u64>,
}

macro_rules! case {
    ($file:expr, $name:expr, $t:ident, $o:ident) => {
        Case { file: $file, name: $name, t: $t, o: |r, b| $o(r, b) }
    };
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = args.get(1).expect("usage: ondemand_bench DIR [SECONDS]");
    let budget: f64 = args.get(2).map_or(1.0, |s| s.parse().unwrap());
    let cases = [
        case!("twitter", "partial_tweets (8 fields per tweet)", t_partial_tweets, o_partial_tweets),
        case!("twitter", "user ids of tweets and retweets", t_user_ids, o_user_ids),
        case!("twitter", "find one tweet by id (halfway)", t_find_tweet, o_find_tweet),
        case!("twitter", "one field at the end", t_tail, o_tail),
        case!("citm_catalog", "performances: ids, start, prices", t_performances, o_performances),
        case!("citm_catalog", "events: id and name", t_events, o_events),
        case!("github_events", "type, time, actor, repo per event", t_events_gh, o_events_gh),
        case!("gsoc-2018", "project and sponsor names", t_gsoc, o_gsoc),
        case!("canada", "feature names only (header)", t_names, o_names),
        case!("canada", "sum every coordinate", t_coords, o_coords),
        case!("mesh", "positions and indices", t_mesh, o_mesh),
        case!("twitter", "read everything", t_walk, o_walk),
        case!("citm_catalog", "read everything", t_walk, o_walk),
        case!("github_events", "read everything", t_walk, o_walk),
        case!("gsoc-2018", "read everything", t_walk, o_walk),
        case!("canada", "read everything", t_walk, o_walk),
        case!("mesh", "read everything", t_walk, o_walk),
    ];
    println!("file\tpattern\tMB\teager us\tlazy us\tondemand us\tstage1 us\tondemand x");
    for c in &cases {
        let data = std::fs::read(format!("{dir}/{}.json", c.file)).unwrap();
        let d = &data[..];
        let mut pe = verilith_json::Parser::new();
        let mut pl = verilith_json::Parser::lazy();
        let mut idx = Vec::new();
        let mut buf = Vec::new();
        let mut best = [f64::MAX; 4];
        let mut sum = [0u64; 3];
        let t0 = Instant::now();
        let mut rounds = 0;
        while rounds < 5 || t0.elapsed().as_secs_f64() < budget {
            for i in 0..4 {
                let t = Instant::now();
                let r = match i {
                    0 => (c.t)(pe.parse(black_box(d)).unwrap().root()),
                    1 => (c.t)(pl.parse(black_box(d)).unwrap().root()),
                    2 => (c.o)(&mut Reader::new(black_box(d), &mut idx).unwrap(), &mut buf).unwrap(),
                    _ => verilith_json::ondemand::index_for(black_box(d), &mut idx).unwrap().0 as u64,
                };
                let e = t.elapsed().as_secs_f64();
                black_box(r);
                if i < 3 {
                    sum[i] = r;
                }
                best[i] = best[i].min(e);
            }
            rounds += 1;
        }
        assert!(sum.iter().all(|&s| s == sum[0]), "{} {}: checksums differ: {sum:x?}", c.file, c.name);
        let base = best[0].min(best[1]);
        print!("{}\t{}\t{:.2}", c.file, c.name, d.len() as f64 / 1e6);
        for b in best {
            print!("\t{:.1}", b * 1e6);
        }
        println!("\t{:.2}", base / best[2]);
    }
}
