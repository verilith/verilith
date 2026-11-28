# bench/run-dnssec.sh 3, cloud x86-64 container (4 vCPUs), 2026-11-28

Unbound 1.19.2 (bench/unbound-dnssec.conf: validator, aggressive-nsec off), dnsperf 2.14.0 with DO set. Both resolvers have the hierarchy's root DS as their only trust anchor. Each round starts the resolvers afresh; the dig check ran in round 1.

| round | resolver | UDP hits q/s | CPU µs/hit | UDP cold q/s (validating) | cold NXDOMAIN latency µs |
|---|---|---|---|---|---|
| 1 | verilith | 426805 | 4.47 | 7415 | 2903 |
| 1 | unbound | 379363 | 4.75 | 10224 | 2504 |
| 2 | unbound | 350209 | 4.87 | 9591 | 2954 |
| 2 | verilith | 412344 | 4.34 | 15256 | 3020 |
| 3 | verilith | 447100 | 4.19 | 17000 | 2658 |
| 3 | unbound | 356998 | 4.62 | 12001 | 2228 |

```
verilith www.example.com: NOERROR qr rd ra ad
verilith foo.wild.example.com: NOERROR qr rd ra ad
verilith nx.example.com: NXDOMAIN qr rd ra ad
verilith www.n3: NOERROR qr rd ra ad
verilith nx.n3: NXDOMAIN qr rd ra ad
verilith www.unsigned.com: NOERROR qr rd ra
verilith www.bad.com: SERVFAIL qr rd ra
verilith www.expired.com: SERVFAIL qr rd ra
unbound www.example.com: NOERROR qr rd ra ad
unbound foo.wild.example.com: NOERROR qr rd ra ad
unbound nx.example.com: NXDOMAIN qr rd ra ad
unbound www.n3: NOERROR qr rd ra ad
unbound nx.n3: NXDOMAIN qr rd ra ad
unbound www.unsigned.com: NOERROR qr rd ra
unbound www.bad.com: SERVFAIL qr rd ra
unbound www.expired.com: SERVFAIL qr rd ra
```
