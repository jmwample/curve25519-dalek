use super::*;
use hex::FromHex;

fn from_hex_be(s: &str) -> [u8; 32] {
    <[u8; 32]>::from_hex(s).expect("failed to unhex")
}

const CURVE25519_ELL2_REP_BE: [&str; 14] = [
    "0000000000000000000000000000000000000000000000000000000000000000",
    "0000000000000000000000000000000000000000000000000000000000000040",
    "0000000000000000000000000000000000000000000000000000000000000080",
    "00000000000000000000000000000000000000000000000000000000000000c0",
    "673a505e107189ee54ca93310ac42e4545e9e59050aaac6f8b5f64295c8ec02f",
    "922688fa428d42bc1fa8806998fbc5959ae801817e85a42a45e8ec25a0d7545a",
    "0d3b0eb88b74ed13d5f6a130e03c4ad607817057dc227152827c0506a538bbba",
    "01a3ea5658f4e00622eeacf724e0bd82068992fae66ed2b04a8599be16662ef5",
    "69599ab5a829c3e9515128d368da7354a8b69fcee4e34d0a668b783b6cae550f",
    "9172922f96d2fa41ea0daf961857056f1656ab8406db80eaeae76af58f8c9f50",
    "6850a20ac5b6d2fa7af7042ad5be234d3311b9fb303753dd2b610bd566983281",
    "84417826c0e80af7cb25a73af1ba87594ff7048a26248b5757e52f2824e068f1",
    "b0fbe152849f49034d2fa00ccc7b960fad7b30b6c4f9f2713eb01c147146ad31",
    "a0ca9ff75afae65598630b3b93560834c7f4dd29a557aa29c7becd49aeef3753",
];

#[test]
fn u255_ignores_only_msb() {
    for (i, s) in CURVE25519_ELL2_REP_BE.iter().enumerate() {
        let u = from_hex_be(s);

        let p0 = MontgomeryPoint::map_to_point_u255(&u).0;

        let mut u_msb = u;
        u_msb[31] ^= 0x80; // flip MSB
        let p1 = MontgomeryPoint::map_to_point_u255(&u_msb).0;

        assert_eq!(p0, p1, "({i}) MSB flip must not change u255 mapping");
    }
}

#[test]
fn u255_is_sensitive_to_second_msb_statistically() {
    let mut changed = 0usize;

    for (i, s) in CURVE25519_ELL2_REP_BE.iter().enumerate() {
        let u = from_hex_be(s);

        let p0 = MontgomeryPoint::map_to_point_u255(&u).0;

        let mut u_40 = u;
        u_40[31] ^= 0x40; // flip 2nd MSB
        let p1 = MontgomeryPoint::map_to_point_u255(&u_40).0;

        if p0 != p1 {
            changed += 1;
        } else {
            // Не фейлим сразу: это "статистический" тест.
            eprintln!("({i}) collision / no-change for 0x40 flip");
        }
    }

    assert!(
        changed >= 10,
        "expected most cases to change when flipping 0x40; changed={changed}/{}",
        CURVE25519_ELL2_REP_BE.len()
    );
}

#[test]
fn rfc9380_map_masks_top_two_bits() {
    for (i, s) in CURVE25519_ELL2_REP_BE.iter().enumerate() {
        let u = from_hex_be(s);

        let p0 = MontgomeryPoint::map_to_point(&u).0;

        let mut u_40 = u;
        u_40[31] ^= 0x40;
        let p1 = MontgomeryPoint::map_to_point(&u_40).0;

        let mut u_80 = u;
        u_80[31] ^= 0x80;
        let p2 = MontgomeryPoint::map_to_point(&u_80).0;

        assert_eq!(p0, p1, "({i}) map_to_point must ignore 0x40");
        assert_eq!(p0, p2, "({i}) map_to_point must ignore 0x80");
    }
}
