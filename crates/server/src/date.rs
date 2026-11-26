//! The `Date` field value (RFC 9110 §5.6.7, IMF-fixdate), formatted once a
//! second per worker.

const DAYS: [&[u8; 3]; 7] = [b"Thu", b"Fri", b"Sat", b"Sun", b"Mon", b"Tue", b"Wed"];
const MONTHS: [&[u8; 3]; 12] =
    [b"Jan", b"Feb", b"Mar", b"Apr", b"May", b"Jun", b"Jul", b"Aug", b"Sep", b"Oct", b"Nov", b"Dec"];

/// `Sun, 06 Nov 1994 08:49:37 GMT` for `t` seconds since the epoch.
pub fn imf_fixdate(t: i64) -> [u8; 29] {
    let days = t.div_euclid(86400);
    let secs = t.rem_euclid(86400);
    let (y, m, d) = civil_from_days(days);
    let wd = days.rem_euclid(7) as usize;
    let mut o = [0u8; 29];
    o[0..3].copy_from_slice(DAYS[wd]);
    o[3] = b',';
    o[4] = b' ';
    two(&mut o[5..7], d as u32);
    o[7] = b' ';
    o[8..11].copy_from_slice(MONTHS[(m - 1) as usize]);
    o[11] = b' ';
    let y = y.clamp(0, 9999) as u32;
    two(&mut o[12..14], y / 100);
    two(&mut o[14..16], y % 100);
    o[16] = b' ';
    two(&mut o[17..19], (secs / 3600) as u32);
    o[19] = b':';
    two(&mut o[20..22], ((secs / 60) % 60) as u32);
    o[22] = b':';
    two(&mut o[23..25], (secs % 60) as u32);
    o[25..29].copy_from_slice(b" GMT");
    o
}

fn two(o: &mut [u8], v: u32) {
    o[0] = b'0' + (v / 10) as u8;
    o[1] = b'0' + (v % 10) as u8;
}

/// Howard Hinnant's days-to-civil algorithm.
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719468;
    let era = z.div_euclid(146097);
    let doe = z.rem_euclid(146097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}

#[cfg(test)]
mod tests {
    #[test]
    fn rfc_example() {
        assert_eq!(&super::imf_fixdate(784111777), b"Sun, 06 Nov 1994 08:49:37 GMT");
        assert_eq!(&super::imf_fixdate(0), b"Thu, 01 Jan 1970 00:00:00 GMT");
        assert_eq!(&super::imf_fixdate(951782400), b"Tue, 29 Feb 2000 00:00:00 GMT");
    }
}
