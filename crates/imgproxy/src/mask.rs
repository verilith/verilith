//! libvips's convolution masks, built in floating point as libvips builds
//! them: `vips_gaussmat` (`create/gaussmat.c`) and the 8-bit fixed-point
//! form `vips_convi_intize` (`convolution/convi.c`) makes for its vector
//! path. Not verified: `filter`'s proofs hold for every table and divisor
//! these give, so a wrong value changes how the image looks, never what
//! the code may do. The arithmetic follows the C line by line (`f64` for
//! `double`, `round_ties_even` for `rint`).

/// `MASK_SANITY` in `gaussmat.c`.
const MASK_SANITY: i64 = 5000;

/// `vips_gaussmat(sigma, min_ampl, separable, integer precision)`: the
/// one-dimensional mask and its scale (the sum of its entries); `None`
/// where libvips fails with "mask too large".
pub fn gaussmat(sigma: f64, min_ampl: f64) -> Option<(Vec<u32>, u32)> {
    let sig2 = 2.0 * sigma * sigma;
    // `int max_x = VIPS_CLIP(0, 8 * sigma, MASK_SANITY)`: a double
    // truncated to an int.
    let max_x = (8.0 * sigma).clamp(0.0, MASK_SANITY as f64) as i64;
    let mut x = 0i64;
    while x < max_x {
        let v = (-((x * x) as f64) / sig2).exp();
        if v < min_ampl {
            break;
        }
        x += 1;
    }
    if x >= MASK_SANITY {
        return None;
    }
    let width = 2 * (x - 1).max(0) + 1;
    let mut m = Vec::with_capacity(width as usize);
    let mut sum = 0.0f64;
    for i in 0..width {
        let xo = i - width / 2;
        let v = (-((xo * xo) as f64) / sig2).exp();
        let v = (20.0 * v).round_ties_even();
        sum += v;
        m.push(v as u32);
    }
    if sum == 0.0 {
        sum = 1.0;
    }
    Some((m, sum as u32))
}

/// The weights and divisor libvips convolves 8-bit images with, for the
/// mask `m` with scale `scale` (offset 0): `vips_convi_intize`'s 8-bit
/// mantissas and `2^exp` when it accepts the mask (its vector path,
/// libvips's default for 8-bit images), else the mask itself and its
/// scale (its C path). Both round as `(sum + d / 2) / d`.
pub fn convi(m: &[u32], scale: u32) -> (Vec<u32>, i64) {
    match intize(m, scale as f64) {
        Some(r) => r,
        None => (m.to_vec(), (scale.max(1)) as i64),
    }
}

fn intize(m: &[u32], scale: f64) -> Option<(Vec<u32>, i64)> {
    let n = m.len();
    let scaled: Vec<f64> = m.iter().map(|&v| v as f64 / scale).collect();
    let mx = scaled.iter().cloned().fold(scaled[0], f64::max);
    if !(mx > 0.0) {
        // log2 of 0 or less: undefined in the C; never so for a gaussmat.
        return None;
    }
    let shift = (mx.log2() + 1.0).ceil() as i32;
    if !(-24..=6).contains(&shift) {
        return None;
    }
    if (n as f64).log2().ceil() > 10.0 {
        return None;
    }
    let exp = 7 - shift;
    let mut mant = Vec::with_capacity(n);
    for &v in &scaled {
        let mi = (128.0 * v * 2f64.powi(-shift)).round_ties_even() as i32;
        if !(-128..=127).contains(&mi) {
            return None;
        }
        mant.push(mi);
    }
    let true_sum: f64 = scaled.iter().zip(&mant).filter(|(_, mi)| **mi != 0).map(|(&s, _)| 128.0 * s).sum();
    let int_sum: i32 = mant.iter().map(|&mi| 128 * mi).sum();
    // `int true_value = VIPS_CLIP(0, true_sum, 255)`: truncated.
    let true_value = true_sum.clamp(0.0, 255.0) as i32;
    let int_value = ((int_sum + (1 << (exp - 1))) >> exp).clamp(0, 255);
    if (true_value - int_value).abs() > 2 {
        return None;
    }
    // A Gaussian's mantissas are never negative.
    Some((mant.iter().map(|&mi| mi.max(0) as u32).collect(), 1i64 << exp))
}

/// `vips_gaussblur(sigma)` as weights and divisor for `filter::blur_rgba`:
/// `Ok(None)` where it copies the image (sigma below 0.2), `Err` where
/// libvips fails.
pub fn gaussblur(sigma: f64) -> Result<Option<(Vec<u32>, i64)>, ()> {
    if sigma < 0.2 {
        return Ok(None);
    }
    let (m, scale) = gaussmat(sigma, 0.2).ok_or(())?;
    Ok(Some(convi(&m, scale)))
}
