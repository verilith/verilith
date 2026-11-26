# 0-RTT: time to the first response byte

`bench/server/zero-rtt` (a rustls 0.23 client) through an in-process proxy
that delays each direction by half the round trip, against
`verilith-server --tls 18443 --early-data 16384 --threads 2` (cloud VM,
loopback). Median of 20 connections each; the TCP connect to the proxy is
not delayed, so a real network adds one round trip to every row.

    cargo run --release --manifest-path bench/server/zero-rtt/Cargo.toml -- 18443 ca.pem 20

| round trip | full handshake | resumed | resumed + 0-RTT |
|---|---|---|---|
| 20 ms | 42.8 ms | 42.5 ms | **21.7 ms** |
| 50 ms | 103.1 ms | 102.8 ms | **51.6 ms** |

Every 0-RTT connection's early data was accepted
(`is_early_data_accepted`). The certificate is
`crates/tls-aws-lc/tests/data` (leaf and CA, converted to PEM).
