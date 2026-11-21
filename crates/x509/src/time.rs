//! Verified UTCTime and GeneralizedTime decoding (RFC 5280 §4.1.2.5).
use crate::der::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A calendar time in UTC, to the second.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Time {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
}

impl View for Time {
    type V = SpecTime;

    open spec fn view(&self) -> SpecTime {
        SpecTime {
            year: self.year,
            month: self.month,
            day: self.day,
            hour: self.hour,
            minute: self.minute,
            second: self.second,
        }
    }
}

#[inline(always)]
fn dd2(c: &[u8], i: usize) -> (r: u8)
    requires
        i + 1 < c@.len(),
        is_digit(c@[i as int]),
        is_digit(c@[i + 1]),
    ensures
        r as int == dd(c@, i as int),
        r <= 99,
{
    (c[i] - 0x30) * 10 + (c[i + 1] - 0x30)
}

#[inline(always)]
fn check_digits(c: &[u8], n: usize) -> (r: bool)
    requires
        n <= c@.len(),
    ensures
        r == all_digits(c@, n as int),
{
    // No early exit: the loop has a fixed trip count at each call, and a
    // certificate's times are almost always digits.
    let mut i: usize = 0;
    let mut ok = true;
    while i < n
        invariant
            n <= c@.len(),
            i <= n,
            ok == forall|j: int| 0 <= j < i ==> is_digit(#[trigger] c@[j]),
        decreases n - i,
    {
        let b = at(c, i);
        let ghost ok0 = ok;
        ok = ok & (b >= 0x30) & (b <= 0x39);
        proof {
            if ok0 && !ok {
                assert(!is_digit(c@[i as int]));
            }
        }
        i = i + 1;
    }
    ok
}

#[inline(always)]
fn days_in(y: u16, m: u8) -> (r: u8)
    ensures
        r as int == days_in_month(y as int, m as int),
{
    if m == 2 {
        if y % 4 == 0 && (y % 100 != 0 || y % 400 == 0) {
            29
        } else {
            28
        }
    } else if m == 4 || m == 6 || m == 9 || m == 11 {
        30
    } else {
        31
    }
}

fn read_time_tail(c: &[u8], i: usize, year: u16) -> (r: Option<Time>)
    requires
        i <= 4,
        c@.len() == i + 11,
        forall|j: int| i <= j < i + 10 ==> is_digit(#[trigger] c@[j]),
    ensures
        r matches Some(t) ==> parse_time_tail(c@, i as int, year as int) == Some(t@),
        r is None ==> parse_time_tail(c@, i as int, year as int) is None,
{
    let mo = dd2(c, i);
    let d = dd2(c, i + 2);
    let h = dd2(c, i + 4);
    let mi = dd2(c, i + 6);
    let se = dd2(c, i + 8);
    if c[i + 10] != 0x5A {
        return None;
    }
    if mo < 1 || mo > 12 || d < 1 || d > days_in(year, mo) || h > 23 || mi > 59 || se > 59 {
        return None;
    }
    Some(Time { year, month: mo, day: d, hour: h, minute: mi, second: se })
}

/// `Time ::= CHOICE { utcTime UTCTime, generalTime GeneralizedTime }`
pub fn read_time(x: Tlv) -> (r: Option<Time>)
    ensures
        r matches Some(t) ==> parse_time(x@) == Some(t@),
        r is None ==> parse_time(x@) is None,
{
    let c = x.content;
    if tag_is(x.tag, 0x17) {
        if c.len() != 13 || !check_digits(c, 12) {
            return None;
        }
        let yy = dd2(c, 0) as u16;
        read_time_tail(
            c,
            2,
            if yy < 50 {
                2000 + yy
            } else {
                1900 + yy
            },
        )
    } else if tag_is(x.tag, 0x18) {
        if c.len() != 15 || !check_digits(c, 14) {
            return None;
        }
        let y = (dd2(c, 0) as u16) * 100 + dd2(c, 2) as u16;
        read_time_tail(c, 4, y)
    } else {
        None
    }
}

} // verus!
