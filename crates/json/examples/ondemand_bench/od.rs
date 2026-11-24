//! The access patterns' view of `verilith_json::ondemand::Reader`: its errors
//! folded into one type, and two helpers the patterns use.
use verilith_json::ondemand::Reader;

#[derive(Debug)]
pub struct E;
pub type R<T> = Result<T, E>;

/// The reader interface the access patterns are written against.
pub trait Od<'a> {
    fn peek(&self) -> u8;
    fn arr_begin(&mut self) -> R<()>;
    fn arr_next(&mut self) -> R<bool>;
    fn obj_begin(&mut self) -> R<()>;
    fn obj_next(&mut self) -> R<bool>;
    fn leave(&mut self, close: u8) -> R<()>;
    fn key_skip(&mut self) -> R<()>;
    fn key_len(&mut self, buf: &mut Vec<u8>) -> R<usize>;
    fn key_is2(&mut self, k1: &[u8], k2: &[u8], m1: &mut bool, m2: &mut bool) -> R<bool>;
    fn find(&mut self, key: &[u8]) -> R<bool>;
    fn str<'b>(&mut self, buf: &'b mut Vec<u8>) -> R<&'b [u8]>
    where
        'a: 'b;
    fn f64(&mut self) -> R<f64>;
    fn i64(&mut self) -> R<i64>;
    fn null(&mut self) -> R<bool>;
    fn bool(&mut self) -> R<bool>;
}


#[inline(always)]
fn m<T>(r: Result<T, verilith_json::ondemand::Mismatch>) -> R<T> {
    r.map_err(|_| E)
}

impl<'a> Od<'a> for Reader<'a> {
    #[inline(always)]
    fn peek(&self) -> u8 {
        Reader::peek(self)
    }
    #[inline(always)]
    fn arr_begin(&mut self) -> R<()> {
        m(Reader::arr_begin(self))
    }
    #[inline(always)]
    fn arr_next(&mut self) -> R<bool> {
        m(Reader::arr_next(self))
    }
    #[inline(always)]
    fn obj_begin(&mut self) -> R<()> {
        m(Reader::obj_begin(self))
    }
    #[inline(always)]
    fn obj_next(&mut self) -> R<bool> {
        m(Reader::obj_next(self))
    }
    #[inline(always)]
    fn leave(&mut self, _close: u8) -> R<()> {
        m(Reader::leave(self))
    }
    #[inline(always)]
    fn key_skip(&mut self) -> R<()> {
        m(Reader::key_skip(self))
    }
    #[inline(always)]
    fn key_len(&mut self, _buf: &mut Vec<u8>) -> R<usize> {
        m(Reader::key(self)).map(|k| k.len())
    }
    #[inline(always)]
    fn key_is2(&mut self, k1: &[u8], k2: &[u8], m1: &mut bool, m2: &mut bool) -> R<bool> {
        let k = m(Reader::key(self))?;
        *m1 = k == k1;
        *m2 = k == k2;
        Ok(*m1 || *m2)
    }
    #[inline(always)]
    fn find(&mut self, key: &[u8]) -> R<bool> {
        m(Reader::find(self, key))
    }
    #[inline(always)]
    fn str<'b>(&mut self, buf: &'b mut Vec<u8>) -> R<&'b [u8]>
    where
        'a: 'b,
    {
        m(Reader::str(self, buf))
    }
    #[inline(always)]
    fn f64(&mut self) -> R<f64> {
        m(Reader::f64(self))
    }
    #[inline(always)]
    fn i64(&mut self) -> R<i64> {
        m(Reader::i64(self))
    }
    #[inline(always)]
    fn null(&mut self) -> R<bool> {
        Ok(Reader::null(self))
    }
    #[inline(always)]
    fn bool(&mut self) -> R<bool> {
        m(Reader::bool(self))
    }
}
