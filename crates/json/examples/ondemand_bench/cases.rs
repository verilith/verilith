//! The access patterns, each written twice: against the tape (`verilith_json::Value`)
//! and against the on-demand reader. Both return the same checksum.
use crate::od::{Od, E, R};
use verilith_json::{Type, Value};

pub const FIND_ID: i64 = 505874879103520768; // statuses[50] of twitter.json

fn slen(v: Option<Value>) -> u64 {
    v.and_then(|v| v.as_bytes()).map_or(0, |b| b.len() as u64)
}
fn int(v: Option<Value>) -> u64 {
    v.and_then(|v| v.as_i64()).unwrap_or(0) as u64
}

// ---- twitter ---------------------------------------------------------------

/// simdjson's `partial_tweets`: eight fields of every tweet.
pub fn t_partial_tweets(root: Value) -> u64 {
    let mut a = 0u64;
    for t in root.get("statuses").unwrap().elements().unwrap() {
        a = a.wrapping_add(slen(t.get("created_at")));
        a = a.wrapping_add(int(t.get("id")));
        a = a.wrapping_add(slen(t.get("text")));
        a = a.wrapping_add(int(t.get("in_reply_to_status_id")));
        let u = t.get("user").unwrap();
        a = a.wrapping_add(int(u.get("id")));
        a = a.wrapping_add(slen(u.get("screen_name")));
        a = a.wrapping_add(int(t.get("retweet_count")));
        a = a.wrapping_add(int(t.get("favorite_count")));
    }
    a
}

fn opt_int<'a, T: Od<'a>>(r: &mut T) -> R<u64> {
    if r.null()? {
        Ok(0)
    } else {
        Ok(r.i64()? as u64)
    }
}

pub fn o_partial_tweets<'a, T: Od<'a>>(r: &mut T, buf: &mut Vec<u8>) -> R<u64> {
    let mut a = 0u64;
    r.obj_begin()?;
    if !r.find(b"statuses")? {
        return Err(E);
    }
    r.arr_begin()?;
    while r.arr_next()? {
        r.obj_begin()?;
        let f = |r: &mut T, k: &[u8]| if r.find(k)? { Ok(()) } else { Err(E) };
        f(r, b"created_at")?;
        a = a.wrapping_add(r.str(buf)?.len() as u64);
        f(r, b"id")?;
        a = a.wrapping_add(r.i64()? as u64);
        f(r, b"text")?;
        a = a.wrapping_add(r.str(buf)?.len() as u64);
        f(r, b"in_reply_to_status_id")?;
        a = a.wrapping_add(opt_int(r)?);
        f(r, b"user")?;
        r.obj_begin()?;
        f(r, b"id")?;
        a = a.wrapping_add(r.i64()? as u64);
        f(r, b"screen_name")?;
        a = a.wrapping_add(r.str(buf)?.len() as u64);
        r.leave(b'}')?;
        f(r, b"retweet_count")?;
        a = a.wrapping_add(r.i64()? as u64);
        f(r, b"favorite_count")?;
        a = a.wrapping_add(r.i64()? as u64);
        r.leave(b'}')?;
    }
    Ok(a)
}

/// simdjson's `find_tweet`: the text of the tweet with a given id.
pub fn t_find_tweet(root: Value) -> u64 {
    for t in root.get("statuses").unwrap().elements().unwrap() {
        if t.get("id").and_then(|v| v.as_i64()) == Some(FIND_ID) {
            return slen(t.get("text"));
        }
    }
    0
}

pub fn o_find_tweet<'a, T: Od<'a>>(r: &mut T, buf: &mut Vec<u8>) -> R<u64> {
    r.obj_begin()?;
    if !r.find(b"statuses")? {
        return Err(E);
    }
    r.arr_begin()?;
    while r.arr_next()? {
        r.obj_begin()?;
        if r.find(b"id")? && r.i64()? == FIND_ID {
            if !r.find(b"text")? {
                return Err(E);
            }
            return Ok(r.str(buf)?.len() as u64);
        }
        r.leave(b'}')?;
    }
    Ok(0)
}

/// simdjson's `distinct_user_id`: the user id of every tweet and retweet.
pub fn t_user_ids(root: Value) -> u64 {
    let mut a = 0u64;
    for t in root.get("statuses").unwrap().elements().unwrap() {
        a = a.wrapping_add(int(t.get("user").unwrap().get("id")));
        if let Some(rt) = t.get("retweeted_status") {
            a = a.wrapping_add(int(rt.get("user").unwrap().get("id")));
        }
    }
    a
}

pub fn o_user_ids<'a, T: Od<'a>>(r: &mut T, _buf: &mut Vec<u8>) -> R<u64> {
    let mut a = 0u64;
    r.obj_begin()?;
    if !r.find(b"statuses")? {
        return Err(E);
    }
    r.arr_begin()?;
    while r.arr_next()? {
        r.obj_begin()?;
        // `user` comes before `retweeted_status`; one forward pass.
        while r.obj_next()? {
            let (mut user, mut rt) = (false, false);
            // Two candidate keys: compare the raw key once against each.
            if r.key_is2(b"user", b"retweeted_status", &mut user, &mut rt)? {
                if user {
                    a = a.wrapping_add(user_id(r)?);
                } else if rt {
                    r.obj_begin()?;
                    if !r.find(b"user")? {
                        return Err(E);
                    }
                    a = a.wrapping_add(user_id(r)?);
                    r.leave(b'}')?;
                }
            }
        }
    }
    Ok(a)
}

fn user_id<'a, T: Od<'a>>(r: &mut T) -> R<u64> {
    r.obj_begin()?;
    if !r.find(b"id")? {
        return Err(E);
    }
    let v = r.i64()? as u64;
    r.leave(b'}')?;
    Ok(v)
}

/// One field at the end of the document: `search_metadata.count`.
pub fn t_tail(root: Value) -> u64 {
    int(root.get("search_metadata").unwrap().get("count"))
}

pub fn o_tail<'a, T: Od<'a>>(r: &mut T, _buf: &mut Vec<u8>) -> R<u64> {
    r.obj_begin()?;
    if !r.find(b"search_metadata")? {
        return Err(E);
    }
    r.obj_begin()?;
    if !r.find(b"count")? {
        return Err(E);
    }
    Ok(r.i64()? as u64)
}

// ---- citm_catalog ----------------------------------------------------------

/// Every performance's ids, start time and prices (seat maps skipped).
pub fn t_performances(root: Value) -> u64 {
    let mut a = 0u64;
    for p in root.get("performances").unwrap().elements().unwrap() {
        a = a.wrapping_add(int(p.get("eventId")));
        a = a.wrapping_add(int(p.get("id")));
        for pr in p.get("prices").unwrap().elements().unwrap() {
            a = a.wrapping_add(int(pr.get("amount")));
        }
        a = a.wrapping_add(int(p.get("start")));
    }
    a
}

pub fn o_performances<'a, T: Od<'a>>(r: &mut T, _buf: &mut Vec<u8>) -> R<u64> {
    let mut a = 0u64;
    r.obj_begin()?;
    if !r.find(b"performances")? {
        return Err(E);
    }
    r.arr_begin()?;
    while r.arr_next()? {
        r.obj_begin()?;
        let f = |r: &mut T, k: &[u8]| if r.find(k)? { Ok(()) } else { Err(E) };
        f(r, b"eventId")?;
        a = a.wrapping_add(r.i64()? as u64);
        f(r, b"id")?;
        a = a.wrapping_add(r.i64()? as u64);
        f(r, b"prices")?;
        r.arr_begin()?;
        while r.arr_next()? {
            r.obj_begin()?;
            f(r, b"amount")?;
            a = a.wrapping_add(r.i64()? as u64);
            r.leave(b'}')?;
        }
        f(r, b"start")?;
        a = a.wrapping_add(r.i64()? as u64);
        r.leave(b'}')?;
    }
    Ok(a)
}

/// Every event's id and name.
pub fn t_events(root: Value) -> u64 {
    let mut a = 0u64;
    for (_, e) in root.get("events").unwrap().members().unwrap() {
        a = a.wrapping_add(int(e.get("id")));
        a = a.wrapping_add(slen(e.get("name")));
    }
    a
}

pub fn o_events<'a, T: Od<'a>>(r: &mut T, buf: &mut Vec<u8>) -> R<u64> {
    let mut a = 0u64;
    r.obj_begin()?;
    if !r.find(b"events")? {
        return Err(E);
    }
    r.obj_begin()?;
    while r.obj_next()? {
        r.key_skip()?;
        r.obj_begin()?;
        if !r.find(b"id")? {
            return Err(E);
        }
        a = a.wrapping_add(r.i64()? as u64);
        if !r.find(b"name")? {
            return Err(E);
        }
        a = a.wrapping_add(r.str(buf)?.len() as u64);
        r.leave(b'}')?;
    }
    Ok(a)
}

// ---- canada ----------------------------------------------------------------

/// Sum of every coordinate: reads every number in the file.
pub fn t_coords(root: Value) -> u64 {
    let mut a = 0f64;
    for f in root.get("features").unwrap().elements().unwrap() {
        for ring in f.get("geometry").unwrap().get("coordinates").unwrap().elements().unwrap() {
            for pt in ring.elements().unwrap() {
                for x in pt.elements().unwrap() {
                    a += x.as_f64().unwrap();
                }
            }
        }
    }
    a.to_bits()
}

pub fn o_coords<'a, T: Od<'a>>(r: &mut T, _buf: &mut Vec<u8>) -> R<u64> {
    let mut a = 0f64;
    r.obj_begin()?;
    if !r.find(b"features")? {
        return Err(E);
    }
    r.arr_begin()?;
    while r.arr_next()? {
        r.obj_begin()?;
        if !r.find(b"geometry")? {
            return Err(E);
        }
        r.obj_begin()?;
        if !r.find(b"coordinates")? {
            return Err(E);
        }
        r.arr_begin()?;
        while r.arr_next()? {
            r.arr_begin()?;
            while r.arr_next()? {
                r.arr_begin()?;
                while r.arr_next()? {
                    a += r.f64()?;
                }
            }
        }
        r.leave(b'}')?;
        r.leave(b'}')?;
    }
    Ok(a.to_bits())
}

/// The feature names only: the header of a large GeoJSON file.
pub fn t_names(root: Value) -> u64 {
    let mut a = 0u64;
    for f in root.get("features").unwrap().elements().unwrap() {
        a += slen(f.get("properties").unwrap().get("name"));
    }
    a
}

pub fn o_names<'a, T: Od<'a>>(r: &mut T, buf: &mut Vec<u8>) -> R<u64> {
    let mut a = 0u64;
    r.obj_begin()?;
    if !r.find(b"features")? {
        return Err(E);
    }
    r.arr_begin()?;
    while r.arr_next()? {
        r.obj_begin()?;
        if !r.find(b"properties")? {
            return Err(E);
        }
        r.obj_begin()?;
        if !r.find(b"name")? {
            return Err(E);
        }
        a += r.str(buf)?.len() as u64;
        r.leave(b'}')?;
        r.leave(b'}')?;
    }
    Ok(a)
}

// ---- mesh ------------------------------------------------------------------

/// Positions and indices of a mesh (texture, colours, normals skipped).
pub fn t_mesh(root: Value) -> u64 {
    let mut a = 0f64;
    for x in root.get("positions").unwrap().elements().unwrap() {
        a += x.as_f64().unwrap();
    }
    let mut b = 0u64;
    for x in root.get("indices").unwrap().elements().unwrap() {
        b += x.as_i64().unwrap() as u64;
    }
    a.to_bits() ^ b
}

pub fn o_mesh<'a, T: Od<'a>>(r: &mut T, _buf: &mut Vec<u8>) -> R<u64> {
    let mut a = 0f64;
    r.obj_begin()?;
    if !r.find(b"positions")? {
        return Err(E);
    }
    r.arr_begin()?;
    while r.arr_next()? {
        a += r.f64()?;
    }
    let mut b = 0u64;
    if !r.find(b"indices")? {
        return Err(E);
    }
    r.arr_begin()?;
    while r.arr_next()? {
        b += r.i64()? as u64;
    }
    Ok(a.to_bits() ^ b)
}

// ---- gsoc-2018 -------------------------------------------------------------

/// Every project's name and sponsor name (long descriptions skipped).
pub fn t_gsoc(root: Value) -> u64 {
    let mut a = 0u64;
    for (_, p) in root.members().unwrap() {
        a += slen(p.get("name"));
        a += slen(p.get("sponsor").unwrap().get("name"));
    }
    a
}

pub fn o_gsoc<'a, T: Od<'a>>(r: &mut T, buf: &mut Vec<u8>) -> R<u64> {
    let mut a = 0u64;
    r.obj_begin()?;
    while r.obj_next()? {
        r.key_skip()?;
        r.obj_begin()?;
        if !r.find(b"name")? {
            return Err(E);
        }
        a += r.str(buf)?.len() as u64;
        if !r.find(b"sponsor")? {
            return Err(E);
        }
        r.obj_begin()?;
        if !r.find(b"name")? {
            return Err(E);
        }
        a += r.str(buf)?.len() as u64;
        r.leave(b'}')?;
        r.leave(b'}')?;
    }
    Ok(a)
}

// ---- github_events ---------------------------------------------------------

/// Type, time, actor and repository of every event (payloads skipped).
pub fn t_events_gh(root: Value) -> u64 {
    let mut a = 0u64;
    for e in root.elements().unwrap() {
        a += slen(e.get("type"));
        a += slen(e.get("created_at"));
        a += slen(e.get("actor").unwrap().get("login"));
        a += slen(e.get("repo").unwrap().get("name"));
    }
    a
}

pub fn o_events_gh<'a, T: Od<'a>>(r: &mut T, buf: &mut Vec<u8>) -> R<u64> {
    let mut a = 0u64;
    r.arr_begin()?;
    while r.arr_next()? {
        r.obj_begin()?;
        let f = |r: &mut T, k: &[u8]| if r.find(k)? { Ok(()) } else { Err(E) };
        f(r, b"type")?;
        a += r.str(buf)?.len() as u64;
        f(r, b"created_at")?;
        a += r.str(buf)?.len() as u64;
        f(r, b"actor")?;
        r.obj_begin()?;
        f(r, b"login")?;
        a += r.str(buf)?.len() as u64;
        r.leave(b'}')?;
        f(r, b"repo")?;
        r.obj_begin()?;
        f(r, b"name")?;
        a += r.str(buf)?.len() as u64;
        r.leave(b'}')?;
        r.leave(b'}')?;
    }
    Ok(a)
}

// ---- any file --------------------------------------------------------------

/// Reads every value: sums the numbers and the lengths of keys and strings.
pub fn t_walk(root: Value) -> u64 {
    fn go(v: Value, a: &mut (f64, u64)) {
        match v.kind() {
            Type::Array => v.elements().unwrap().for_each(|e| go(e, a)),
            Type::Object => {
                for (k, e) in v.members().unwrap() {
                    a.1 += k.as_bytes().len() as u64;
                    go(e, a);
                }
            }
            Type::Number => a.0 += v.as_f64().unwrap(),
            Type::String => a.1 += v.as_bytes().unwrap().len() as u64,
            _ => {}
        }
    }
    let mut a = (0.0, 0);
    go(root, &mut a);
    a.0.to_bits() ^ a.1
}

pub fn o_walk<'a, T: Od<'a>>(r: &mut T, buf: &mut Vec<u8>) -> R<u64> {
    fn go<'a, T: Od<'a>>(r: &mut T, buf: &mut Vec<u8>, a: &mut (f64, u64), depth: usize) -> R<()> {
        if depth == 0 {
            return Err(E);
        }
        match r.peek() {
            b'[' => {
                r.arr_begin()?;
                while r.arr_next()? {
                    go(r, buf, a, depth - 1)?;
                }
            }
            b'{' => {
                r.obj_begin()?;
                while r.obj_next()? {
                    a.1 += r.key_len(buf)? as u64;
                    go(r, buf, a, depth - 1)?;
                }
            }
            b'"' => a.1 += r.str(buf)?.len() as u64,
            b't' | b'f' => {
                r.bool()?;
            }
            b'n' => {
                if !r.null()? {
                    return Err(E);
                }
            }
            _ => a.0 += r.f64()?,
        }
        Ok(())
    }
    let mut a = (0.0, 0);
    go(r, buf, &mut a, 1000)?;
    Ok(a.0.to_bits() ^ a.1)
}
