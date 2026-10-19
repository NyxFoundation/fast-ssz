//! SHA-256 of two SSZ nodes, following FIPS 180-4 and the pinned SSZ model.
//! The input is exactly 64 bytes; padding therefore occupies a second fixed block.

const ROUND_CONSTANTS: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

#[derive(Clone, Copy)]
struct State {
    a: u32,
    b: u32,
    c: u32,
    d: u32,
    e: u32,
    f: u32,
    g: u32,
    h: u32,
}

macro_rules! rotr {
    ($word:expr, $right:literal, $left:literal) => {
        ($word >> $right) | ($word << $left)
    };
}

// Explicit shifts mirror the reference rather than an external rotation model.
#[allow(clippy::manual_rotate)]
fn sigma0(x: u32) -> u32 {
    rotr!(x, 7u32, 25u32) ^ rotr!(x, 18u32, 14u32) ^ (x >> 3u32)
}

#[allow(clippy::manual_rotate)]
fn sigma1(x: u32) -> u32 {
    rotr!(x, 17u32, 15u32) ^ rotr!(x, 19u32, 13u32) ^ (x >> 10u32)
}

#[allow(clippy::manual_rotate)]
fn big_sigma0(x: u32) -> u32 {
    rotr!(x, 2u32, 30u32) ^ rotr!(x, 13u32, 19u32) ^ rotr!(x, 22u32, 10u32)
}

#[allow(clippy::manual_rotate)]
fn big_sigma1(x: u32) -> u32 {
    rotr!(x, 6u32, 26u32) ^ rotr!(x, 11u32, 21u32) ^ rotr!(x, 25u32, 7u32)
}

fn choose(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ ((!x) & z)
}

fn majority(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

fn word(a: u8, b: u8, c: u8, d: u8) -> u32 {
    ((a as u32) << 24) | ((b as u32) << 16) | ((c as u32) << 8) | (d as u32)
}

fn input_words(left: &[u8; 32], right: &[u8; 32]) -> [u32; 16] {
    macro_rules! read_words {
        ($($i:literal),+) => {
            [$(word(left[$i], left[$i + 1], left[$i + 2], left[$i + 3])),+,
             $(word(right[$i], right[$i + 1], right[$i + 2], right[$i + 3])),+]
        };
    }
    read_words!(0, 4, 8, 12, 16, 20, 24, 28)
}

fn initial_schedule(initial: &[u32; 16]) -> [u32; 64] {
    let mut words = [0; 64];
    macro_rules! copy_initial {
        ($($i:literal),+) => { $(words[$i] = initial[$i];)+ };
    }
    copy_initial!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
    words
}

fn extend_schedule(words: &mut [u32; 64], index: usize) {
    words[index] = words[index - 16]
        .wrapping_add(sigma0(words[index - 15]))
        .wrapping_add(words[index - 7])
        .wrapping_add(sigma1(words[index - 2]));
}

fn schedule(initial: [u32; 16]) -> [u32; 64] {
    let mut words = initial_schedule(&initial);
    macro_rules! expand_words {
        ($($i:literal),+ $(,)?) => { $(extend_schedule(&mut words, $i);)+ };
    }
    expand_words!(
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38,
        39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61,
        62, 63,
    );
    words
}

fn round(state: State, constant: u32, message: u32) -> State {
    let t1 = state
        .h
        .wrapping_add(big_sigma1(state.e))
        .wrapping_add(choose(state.e, state.f, state.g))
        .wrapping_add(constant)
        .wrapping_add(message);
    let t2 = big_sigma0(state.a).wrapping_add(majority(state.a, state.b, state.c));
    State {
        a: t1.wrapping_add(t2),
        b: state.a,
        c: state.b,
        d: state.c,
        e: state.d.wrapping_add(t1),
        f: state.e,
        g: state.f,
        h: state.g,
    }
}

fn round_at(state: State, words: &[u32; 64], index: usize) -> State {
    round(state, ROUND_CONSTANTS[index], words[index])
}

fn rounds(mut state: State, words: &[u32; 64]) -> State {
    macro_rules! run_rounds {
        ($($i:literal),+ $(,)?) => {
            $(state = round_at(state, words, $i);)+
        };
    }
    run_rounds!(
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
        48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
    );
    state
}

fn compress(initial: State, message: [u32; 16]) -> State {
    let words = schedule(message);
    let working = rounds(initial, &words);
    State {
        a: initial.a.wrapping_add(working.a),
        b: initial.b.wrapping_add(working.b),
        c: initial.c.wrapping_add(working.c),
        d: initial.d.wrapping_add(working.d),
        e: initial.e.wrapping_add(working.e),
        f: initial.f.wrapping_add(working.f),
        g: initial.g.wrapping_add(working.g),
        h: initial.h.wrapping_add(working.h),
    }
}

fn digest(state: State) -> [u8; 32] {
    macro_rules! bytes {
        ($($word:expr),+) => {
            [$(($word >> 24) as u8, ($word >> 16) as u8,
               ($word >> 8) as u8, $word as u8,)+]
        };
    }
    bytes!(state.a, state.b, state.c, state.d, state.e, state.f, state.g, state.h)
}

/// Hash two 32-byte SSZ nodes in left/right order, without allocation or unsafe code.
pub fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let initial = State {
        a: 0x6a09e667,
        b: 0xbb67ae85,
        c: 0x3c6ef372,
        d: 0xa54ff53a,
        e: 0x510e527f,
        f: 0x9b05688c,
        g: 0x1f83d9ab,
        h: 0x5be0cd19,
    };
    let first = compress(initial, input_words(left, right));
    // One delimiter, zero padding, then the 512-bit length of the original message.
    let padding = [0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 512];
    digest(compress(first, padding))
}
