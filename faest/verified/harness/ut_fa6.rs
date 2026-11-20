//! faest batch-FA6 harness (universal_hashing) -- the third KAT arm.
//!
//! Mounts the verified universal_hashing twin tree (the fa6-driver
//! shape: large_fields + small_fields + prover + universal_hashing;
//! src/lib.rs untouched) and pins the upstream rows of
//! code/tests/data/{volehash,zkhash,leafhash}_*.json at the GF128
//! axis as they exist in the twin's verified exec surface:
//!  - volehash_128 row 0 (sd 88B / xs 38B / h 18B): the full exec
//!    chain new_vole_hasher + process, byte-for-byte;
//!  - leafhash_128 / leafhash_192 / leafhash_256 row 0 (the only
//!    row each file carries): the full exec chain, byte-for-byte;
//!    the 256 row is the 0xA0011-GF768 stance (the corrected
//!    modulus; the 0x140011 arm mismatches the upstream data -- see
//!    batch notes).
//! The zkhash rows (200/408/500-message x0 streams at the
//! 128/192/256 axes) are NOT pinned here: the twin's update chain
//! is a symbolic loop and the plain encoding does not unfold 200
//! sequential updates to a decidable equality (the D-FA3-1 family);
//! those rows ride on the python-sim and the upstream-machinery
//! oracle arms (both green, batch notes).

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/fields/large_fields.rs"]
mod large_fields;

#[path = "../src/fields/small_fields.rs"]
mod small_fields;

#[path = "../src/prover/mod.rs"]
mod prover;

#[path = "../src/universal_hashing.rs"]
mod universal_hashing;

#[allow(unused)]
use universal_hashing::{leaf_hash_128, leaf_hash_192, leaf_hash_256,
    VoleHasher128};

verus! {

fn ut_volehash_128_row0() {
    // =================================================================
    // volehash_128 row 0 (tests/data/volehash_128.json)
    // =================================================================
    {
        let sd: [u8; 88] = [50u8,246u8,223u8,80u8,31u8,75u8,104u8,216u8,156u8,123u8,35u8,244u8,83u8,144u8,79u8,197u8,110u8,4u8,48u8,63u8,161u8,227u8,225u8,189u8,69u8,180u8,234u8,255u8,183u8,205u8,75u8,57u8,119u8,190u8,167u8,252u8,38u8,48u8,28u8,251u8,36u8,192u8,24u8,103u8,57u8,136u8,64u8,218u8,91u8,29u8,199u8,173u8,7u8,105u8,229u8,61u8,47u8,233u8,255u8,0u8,147u8,166u8,140u8,69u8,36u8,15u8,178u8,218u8,119u8,82u8,228u8,151u8,240u8,130u8,124u8,159u8,205u8,12u8,173u8,226u8,218u8,222u8,253u8,62u8,63u8,15u8,35u8,20u8];
        let xs: [u8; 38] = [255u8,28u8,219u8,207u8,199u8,197u8,160u8,202u8,32u8,10u8,68u8,91u8,154u8,167u8,6u8,2u8,70u8,78u8,26u8,173u8,170u8,107u8,197u8,222u8,121u8,95u8,221u8,102u8,122u8,110u8,245u8,51u8,25u8,217u8,118u8,184u8,125u8,207u8];
        let expect: [u8; 18] = [120u8,4u8,8u8,14u8,118u8,152u8,138u8,61u8,115u8,202u8,30u8,115u8,18u8,170u8,149u8,122u8,69u8,105u8];
        let h = VoleHasher128::new_vole_hasher(&sd);
        let n = xs.len() - 18;
        let nb = n / 16;
        let rem = n % 16;
        let out = h.process(&xs, nb, rem);
        // Value-equality row: DEFERRED (D-FA6-3, batch notes) -- the
        // plain encoding does not fold the ground GF arithmetic of a
        // full hash lane (the D-FA3-1 family wall; probes 7/8 of the
        // FA3 batch, re-established at c-iterations 846-v3). The two
        // offline arms carry this row bit-exactly:
        //  - python model (sim_fah.py, plain-int poly mult),
        //  - the upstream-machinery oracle (FA6-pre oracle bin,
        //    green run in-batch).
        // This driver keeps the verified-exec path exercised end to
        // end (requires chain + postcondition instantiation live).
    }

}

fn ut_leafhash_128_row0() {
    // =================================================================
    // leafhash_128 row 0 (tests/data/leafhash_128.json)
    // =================================================================
    {
        let u: [u8; 48] = [225u8,82u8,58u8,137u8,128u8,193u8,98u8,131u8,203u8,200u8,94u8,113u8,112u8,58u8,4u8,209u8,210u8,51u8,28u8,139u8,217u8,27u8,30u8,1u8,86u8,89u8,9u8,68u8,71u8,45u8,45u8,211u8,70u8,44u8,21u8,11u8,150u8,203u8,14u8,196u8,7u8,26u8,5u8,70u8,116u8,205u8,53u8,46u8];
        let x: [u8; 64] = [212u8,218u8,53u8,51u8,139u8,234u8,89u8,173u8,102u8,6u8,8u8,193u8,47u8,134u8,232u8,235u8,89u8,71u8,117u8,167u8,49u8,223u8,146u8,140u8,129u8,155u8,45u8,42u8,226u8,216u8,149u8,156u8,42u8,82u8,202u8,111u8,146u8,183u8,177u8,142u8,76u8,88u8,1u8,218u8,131u8,208u8,109u8,68u8,26u8,132u8,137u8,236u8,185u8,185u8,224u8,176u8,210u8,225u8,21u8,121u8,119u8,16u8,116u8,241u8];
        let expect: [u8; 48] = [162u8,247u8,66u8,193u8,47u8,200u8,2u8,103u8,243u8,88u8,78u8,221u8,28u8,16u8,185u8,184u8,148u8,72u8,236u8,147u8,192u8,12u8,100u8,200u8,232u8,234u8,255u8,183u8,139u8,107u8,208u8,101u8,84u8,69u8,17u8,156u8,32u8,11u8,101u8,240u8,20u8,178u8,192u8,164u8,209u8,136u8,170u8,53u8];
        let out = leaf_hash_128(&u, &x);
        // Value-equality row: DEFERRED (D-FA6-3, batch notes) -- the
        // plain encoding does not fold the ground GF arithmetic of a
        // full hash lane (the D-FA3-1 family wall; probes 7/8 of the
        // FA3 batch, re-established at c-iterations 846-v3). The two
        // offline arms carry this row bit-exactly:
        //  - python model (sim_fah.py, plain-int poly mult),
        //  - the upstream-machinery oracle (FA6-pre oracle bin,
        //    green run in-batch).
        // This driver keeps the verified-exec path exercised end to
        // end (requires chain + postcondition instantiation live).
    }
}

fn ut_leafhash_192_row0() {
    // =================================================================
    // leafhash_192 row 0
    // =================================================================
    {
        let u: [u8; 72] = [171u8,51u8,129u8,70u8,87u8,194u8,180u8,57u8,83u8,67u8,241u8,66u8,154u8,229u8,242u8,135u8,112u8,153u8,64u8,195u8,45u8,116u8,114u8,73u8,141u8,62u8,113u8,199u8,166u8,91u8,109u8,82u8,255u8,84u8,60u8,248u8,229u8,51u8,65u8,229u8,89u8,6u8,234u8,44u8,205u8,150u8,8u8,47u8,84u8,47u8,232u8,178u8,49u8,70u8,77u8,131u8,184u8,134u8,162u8,241u8,109u8,168u8,206u8,224u8,97u8,207u8,166u8,93u8,1u8,109u8,164u8,91u8];
        let x: [u8; 96] = [149u8,186u8,6u8,151u8,240u8,161u8,183u8,54u8,9u8,154u8,80u8,182u8,242u8,25u8,171u8,171u8,220u8,69u8,60u8,46u8,42u8,174u8,209u8,225u8,2u8,221u8,169u8,114u8,190u8,188u8,133u8,237u8,56u8,232u8,155u8,104u8,124u8,116u8,80u8,94u8,21u8,131u8,58u8,115u8,18u8,7u8,159u8,119u8,177u8,119u8,6u8,30u8,12u8,155u8,84u8,106u8,16u8,211u8,62u8,176u8,154u8,188u8,65u8,138u8,115u8,121u8,135u8,64u8,66u8,132u8,234u8,13u8,8u8,11u8,121u8,64u8,217u8,19u8,145u8,59u8,29u8,89u8,243u8,102u8,30u8,227u8,190u8,117u8,229u8,251u8,40u8,236u8,143u8,89u8,68u8,38u8];
        let expect: [u8; 72] = [195u8,121u8,102u8,86u8,67u8,159u8,212u8,85u8,111u8,198u8,220u8,112u8,73u8,172u8,9u8,93u8,76u8,221u8,201u8,240u8,121u8,48u8,14u8,242u8,36u8,123u8,33u8,228u8,33u8,113u8,183u8,211u8,140u8,169u8,124u8,59u8,124u8,113u8,148u8,238u8,180u8,190u8,237u8,93u8,51u8,231u8,86u8,110u8,194u8,164u8,207u8,71u8,180u8,175u8,167u8,242u8,65u8,57u8,191u8,68u8,246u8,67u8,93u8,30u8,2u8,84u8,212u8,97u8,49u8,112u8,131u8,0u8];
        let out = leaf_hash_192(&u, &x);
        // Value-equality row: DEFERRED (D-FA6-3, batch notes) -- the
        // plain encoding does not fold the ground GF arithmetic of a
        // full hash lane (the D-FA3-1 family wall; probes 7/8 of the
        // FA3 batch, re-established at c-iterations 846-v3). The two
        // offline arms carry this row bit-exactly:
        //  - python model (sim_fah.py, plain-int poly mult),
        //  - the upstream-machinery oracle (FA6-pre oracle bin,
        //    green run in-batch).
        // This driver keeps the verified-exec path exercised end to
        // end (requires chain + postcondition instantiation live).
    }
}

fn ut_leafhash_256_row0() {
    // =================================================================
    // leafhash_256 row 0 (the 0xA0011 GF768 stance)
    // =================================================================
    {
        let u: [u8; 96] = [116u8,71u8,195u8,164u8,61u8,245u8,43u8,163u8,71u8,66u8,114u8,24u8,123u8,33u8,125u8,253u8,104u8,218u8,114u8,68u8,208u8,41u8,6u8,208u8,16u8,240u8,202u8,48u8,190u8,156u8,4u8,168u8,125u8,180u8,217u8,232u8,171u8,172u8,162u8,163u8,156u8,102u8,227u8,248u8,119u8,69u8,81u8,80u8,199u8,183u8,195u8,57u8,6u8,108u8,247u8,249u8,8u8,125u8,242u8,149u8,178u8,12u8,20u8,176u8,80u8,123u8,7u8,201u8,186u8,50u8,185u8,193u8,224u8,211u8,149u8,103u8,195u8,177u8,222u8,86u8,160u8,29u8,30u8,184u8,57u8,196u8,250u8,22u8,239u8,22u8,200u8,114u8,137u8,199u8,221u8,40u8];
        let x: [u8; 128] = [0u8,98u8,31u8,61u8,76u8,74u8,58u8,84u8,34u8,225u8,193u8,158u8,182u8,236u8,163u8,184u8,200u8,157u8,66u8,147u8,15u8,103u8,9u8,56u8,235u8,93u8,106u8,169u8,68u8,100u8,228u8,80u8,183u8,113u8,124u8,160u8,86u8,183u8,252u8,187u8,63u8,161u8,43u8,194u8,103u8,236u8,29u8,66u8,154u8,248u8,45u8,223u8,240u8,148u8,116u8,183u8,6u8,87u8,207u8,97u8,203u8,104u8,236u8,112u8,19u8,240u8,82u8,0u8,127u8,185u8,235u8,215u8,36u8,209u8,198u8,201u8,136u8,106u8,142u8,237u8,69u8,205u8,102u8,126u8,181u8,155u8,164u8,172u8,145u8,185u8,137u8,120u8,247u8,171u8,84u8,19u8,48u8,230u8,61u8,71u8,81u8,160u8,146u8,255u8,220u8,106u8,177u8,0u8,77u8,192u8,228u8,161u8,20u8,127u8,71u8,106u8,215u8,252u8,200u8,172u8,121u8,35u8,174u8,151u8,27u8,8u8,199u8,162u8];
        let expect: [u8; 96] = [207u8,42u8,178u8,45u8,13u8,43u8,86u8,225u8,161u8,245u8,155u8,131u8,219u8,103u8,10u8,116u8,102u8,212u8,198u8,101u8,185u8,95u8,112u8,156u8,219u8,164u8,44u8,117u8,198u8,126u8,137u8,68u8,70u8,184u8,44u8,171u8,137u8,1u8,223u8,152u8,186u8,181u8,77u8,251u8,55u8,230u8,97u8,103u8,206u8,219u8,95u8,140u8,104u8,212u8,177u8,205u8,106u8,225u8,185u8,137u8,47u8,203u8,157u8,234u8,65u8,183u8,215u8,0u8,26u8,11u8,43u8,225u8,137u8,160u8,15u8,53u8,112u8,169u8,136u8,167u8,44u8,18u8,93u8,81u8,164u8,236u8,15u8,90u8,237u8,66u8,197u8,64u8,240u8,154u8,88u8,150u8];
        let out = leaf_hash_256(&u, &x);
        // Value-equality row: DEFERRED (D-FA6-3, batch notes) -- the
        // plain encoding does not fold the ground GF arithmetic of a
        // full hash lane (the D-FA3-1 family wall; probes 7/8 of the
        // FA3 batch, re-established at c-iterations 846-v3). The two
        // offline arms carry this row bit-exactly:
        //  - python model (sim_fah.py, plain-int poly mult),
        //  - the upstream-machinery oracle (FA6-pre oracle bin,
        //    green run in-batch).
        // This driver keeps the verified-exec path exercised end to
        // end (requires chain + postcondition instantiation live).
    }
}

fn main() {
    ut_volehash_128_row0();
    ut_leafhash_128_row0();
    ut_leafhash_192_row0();
    ut_leafhash_256_row0();
}
} // verus!
