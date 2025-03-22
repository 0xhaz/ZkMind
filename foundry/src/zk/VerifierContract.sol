// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2Verifier {
    uint256 internal constant    DELTA = 4131629893567559867359510883348571134090853742863529169391034518566172092834;
    uint256 internal constant        R = 21888242871839275222246405745257275088548364400416034343698204186575808495617; 

    uint256 internal constant FIRST_QUOTIENT_X_CPTR = 0x4124;
    uint256 internal constant  LAST_QUOTIENT_X_CPTR = 0x4224;

    uint256 internal constant                VK_MPTR = 0x1480;
    uint256 internal constant         VK_DIGEST_MPTR = 0x1480;
    uint256 internal constant     NUM_INSTANCES_MPTR = 0x14a0;
    uint256 internal constant                 K_MPTR = 0x14c0;
    uint256 internal constant             N_INV_MPTR = 0x14e0;
    uint256 internal constant             OMEGA_MPTR = 0x1500;
    uint256 internal constant         OMEGA_INV_MPTR = 0x1520;
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = 0x1540;
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = 0x1560;
    uint256 internal constant        ACC_OFFSET_MPTR = 0x1580;
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = 0x15a0;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x15c0;
    uint256 internal constant              G1_X_MPTR = 0x15e0;
    uint256 internal constant              G1_Y_MPTR = 0x1600;
    uint256 internal constant            G2_X_1_MPTR = 0x1620;
    uint256 internal constant            G2_X_2_MPTR = 0x1640;
    uint256 internal constant            G2_Y_1_MPTR = 0x1660;
    uint256 internal constant            G2_Y_2_MPTR = 0x1680;
    uint256 internal constant      NEG_S_G2_X_1_MPTR = 0x16a0;
    uint256 internal constant      NEG_S_G2_X_2_MPTR = 0x16c0;
    uint256 internal constant      NEG_S_G2_Y_1_MPTR = 0x16e0;
    uint256 internal constant      NEG_S_G2_Y_2_MPTR = 0x1700;

    uint256 internal constant CHALLENGE_MPTR = 0x4ae0;

    uint256 internal constant THETA_MPTR = 0x4ae0;
    uint256 internal constant  BETA_MPTR = 0x4b00;
    uint256 internal constant GAMMA_MPTR = 0x4b20;
    uint256 internal constant     Y_MPTR = 0x4b40;
    uint256 internal constant     X_MPTR = 0x4b60;
    uint256 internal constant  ZETA_MPTR = 0x4b80;
    uint256 internal constant    NU_MPTR = 0x4ba0;
    uint256 internal constant    MU_MPTR = 0x4bc0;

    uint256 internal constant       ACC_LHS_X_MPTR = 0x4be0;
    uint256 internal constant       ACC_LHS_Y_MPTR = 0x4c00;
    uint256 internal constant       ACC_RHS_X_MPTR = 0x4c20;
    uint256 internal constant       ACC_RHS_Y_MPTR = 0x4c40;
    uint256 internal constant             X_N_MPTR = 0x4c60;
    uint256 internal constant X_N_MINUS_1_INV_MPTR = 0x4c80;
    uint256 internal constant          L_LAST_MPTR = 0x4ca0;
    uint256 internal constant         L_BLIND_MPTR = 0x4cc0;
    uint256 internal constant             L_0_MPTR = 0x4ce0;
    uint256 internal constant   INSTANCE_EVAL_MPTR = 0x4d00;
    uint256 internal constant   QUOTIENT_EVAL_MPTR = 0x4d20;
    uint256 internal constant      QUOTIENT_X_MPTR = 0x4d40;
    uint256 internal constant      QUOTIENT_Y_MPTR = 0x4d60;
    uint256 internal constant          R_EVAL_MPTR = 0x4d80;
    uint256 internal constant   PAIRING_LHS_X_MPTR = 0x4da0;
    uint256 internal constant   PAIRING_LHS_Y_MPTR = 0x4dc0;
    uint256 internal constant   PAIRING_RHS_X_MPTR = 0x4de0;
    uint256 internal constant   PAIRING_RHS_Y_MPTR = 0x4e00;

    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) public returns (bool) {
        assembly {
            // Read EC point (x, y) at (proof_cptr, proof_cptr + 0x20),
            // and check if the point is on affine plane,
            // and store them in (hash_mptr, hash_mptr + 0x20).
            // Return updated (success, proof_cptr, hash_mptr).
            function read_ec_point(success, proof_cptr, hash_mptr, q) -> ret0, ret1, ret2 {
                let x := calldataload(proof_cptr)
                let y := calldataload(add(proof_cptr, 0x20))
                ret0 := and(success, lt(x, q))
                ret0 := and(ret0, lt(y, q))
                ret0 := and(ret0, eq(mulmod(y, y, q), addmod(mulmod(x, mulmod(x, x, q), q), 3, q)))
                mstore(hash_mptr, x)
                mstore(add(hash_mptr, 0x20), y)
                ret1 := add(proof_cptr, 0x40)
                ret2 := add(hash_mptr, 0x40)
            }

            // Squeeze challenge by keccak256(memory[0..hash_mptr]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr, hash_mptr).
            function squeeze_challenge(challenge_mptr, hash_mptr, r) -> ret0, ret1 {
                let hash := keccak256(0x00, hash_mptr)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret0 := add(challenge_mptr, 0x20)
                ret1 := 0x20
            }

            // Squeeze challenge without absorbing new input from calldata,
            // by putting an extra 0x01 in memory[0x20] and squeeze by keccak256(memory[0..21]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr).
            function squeeze_challenge_cont(challenge_mptr, r) -> ret {
                mstore8(0x20, 0x01)
                let hash := keccak256(0x00, 0x21)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret := add(challenge_mptr, 0x20)
            }

            // Batch invert values in memory[mptr_start..mptr_end] in place.
            // Return updated (success).
            function batch_invert(success, mptr_start, mptr_end) -> ret {
                let gp_mptr := mptr_end
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for
                    {}
                    lt(mptr, sub(mptr_end, 0x20))
                    {}
                {
                    gp := mulmod(gp, mload(mptr), R)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), R)

                mstore(gp_mptr, 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(R, 2))
                mstore(add(gp_mptr, 0xa0), R)
                ret := and(success, staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20))
                let all_inv := mload(gp_mptr)

                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for
                    {}
                    lt(second_mptr, mptr)
                    {}
                {
                    let inv := mulmod(all_inv, mload(gp_mptr), R)
                    all_inv := mulmod(all_inv, mload(mptr), R)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), R)
                let inv_second := mulmod(all_inv, mload(first_mptr), R)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Add (x, y) into point at (0x00, 0x20).
            // Return updated (success).
            function ec_add_acc(success, x, y) -> ret {
                mstore(0x40, x)
                mstore(0x60, y)
                ret := and(success, staticcall(gas(), 0x06, 0x00, 0x80, 0x00, 0x40))
            }

            // Scale point at (0x00, 0x20) by scalar.
            function ec_mul_acc(success, scalar) -> ret {
                mstore(0x40, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x00, 0x60, 0x00, 0x40))
            }

            // Add (x, y) into point at (0x80, 0xa0).
            // Return updated (success).
            function ec_add_tmp(success, x, y) -> ret {
                mstore(0xc0, x)
                mstore(0xe0, y)
                ret := and(success, staticcall(gas(), 0x06, 0x80, 0x80, 0x80, 0x40))
            }

            // Scale point at (0x80, 0xa0) by scalar.
            // Return updated (success).
            function ec_mul_tmp(success, scalar) -> ret {
                mstore(0xc0, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x80, 0x60, 0x80, 0x40))
            }

            // Perform pairing check.
            // Return updated (success).
            function ec_pairing(success, lhs_x, lhs_y, rhs_x, rhs_y) -> ret {
                mstore(0x00, lhs_x)
                mstore(0x20, lhs_y)
                mstore(0x40, mload(G2_X_1_MPTR))
                mstore(0x60, mload(G2_X_2_MPTR))
                mstore(0x80, mload(G2_Y_1_MPTR))
                mstore(0xa0, mload(G2_Y_2_MPTR))
                mstore(0xc0, rhs_x)
                mstore(0xe0, rhs_y)
                mstore(0x100, mload(NEG_S_G2_X_1_MPTR))
                mstore(0x120, mload(NEG_S_G2_X_2_MPTR))
                mstore(0x140, mload(NEG_S_G2_Y_1_MPTR))
                mstore(0x160, mload(NEG_S_G2_Y_2_MPTR))
                ret := and(success, staticcall(gas(), 0x08, 0x00, 0x180, 0x00, 0x20))
                ret := and(ret, mload(0x00))
            }

            // Modulus
            let q := 21888242871839275222246405745257275088696311157297823662689037894645226208583 // BN254 base field
            let r := 21888242871839275222246405745257275088548364400416034343698204186575808495617 // BN254 scalar field 

            // Initialize success as true
            let success := true

            {
                // Load vk_digest and num_instances of vk into memory
                mstore(0x1480, 0x1f51b817c1298ac4f8a6d31b8e1aa44562256e7a4c303ce2f1b051d54cf85dae) // vk_digest
                mstore(0x14a0, 0x000000000000000000000000000000000000000000000000000000000000000a) // num_instances

                // Check valid length of proof
                success := and(success, eq(0x8d40, proof.length))

                // Check valid length of instances
                let num_instances := mload(NUM_INSTANCES_MPTR)
                success := and(success, eq(num_instances, instances.length))

                // Absorb vk diegst
                mstore(0x00, mload(VK_DIGEST_MPTR))

                // Read instances and witness commitments and generate challenges
                let hash_mptr := 0x20
                let instance_cptr := instances.offset
                for
                    { let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances)) }
                    lt(instance_cptr, instance_cptr_end)
                    {}
                {
                    let instance := calldataload(instance_cptr)
                    success := and(success, lt(instance, r))
                    mstore(hash_mptr, instance)
                    instance_cptr := add(instance_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                let proof_cptr := proof.offset
                let challenge_mptr := CHALLENGE_MPTR

                // Phase 1
                for
                    { let proof_cptr_end := add(proof_cptr, 0x1440) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 2
                for
                    { let proof_cptr_end := add(proof_cptr, 0x1380) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)

                // Phase 3
                for
                    { let proof_cptr_end := add(proof_cptr, 0x1900) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 4
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0140) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Read evaluations
                for
                    { let proof_cptr_end := add(proof_cptr, 0x4ac0) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    let eval := calldataload(proof_cptr)
                    success := and(success, lt(eval, r))
                    mstore(hash_mptr, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                // Read batch opening proof and generate challenges
                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // zeta
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)                        // nu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // mu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W'

                // Load full vk into memory
                mstore(0x1480, 0x1f51b817c1298ac4f8a6d31b8e1aa44562256e7a4c303ce2f1b051d54cf85dae) // vk_digest
                mstore(0x14a0, 0x000000000000000000000000000000000000000000000000000000000000000a) // num_instances
                mstore(0x14c0, 0x0000000000000000000000000000000000000000000000000000000000000011) // k
                mstore(0x14e0, 0x30643640b9f82f90e83b698e5ea6179c7c05542e859533b48b9953a2f5360801) // n_inv
                mstore(0x1500, 0x304cd1e79cfa5b0f054e981a27ed7706e7ea6b06a7f266ef8db819c179c2c3ea) // omega
                mstore(0x1520, 0x193586da872cdeff023d6ab2263a131b4780db8878be3c3b7f8f019c06fcb0fb) // omega_inv
                mstore(0x1540, 0x299110e6835fd73731fb3ce6de87151988da403c265467a96b9cda0d7daa72e4) // omega_inv_to_l
                mstore(0x1560, 0x0000000000000000000000000000000000000000000000000000000000000000) // has_accumulator
                mstore(0x1580, 0x0000000000000000000000000000000000000000000000000000000000000000) // acc_offset
                mstore(0x15a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limbs
                mstore(0x15c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limb_bits
                mstore(0x15e0, 0x0000000000000000000000000000000000000000000000000000000000000001) // g1_x
                mstore(0x1600, 0x0000000000000000000000000000000000000000000000000000000000000002) // g1_y
                mstore(0x1620, 0x198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2) // g2_x_1
                mstore(0x1640, 0x1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed) // g2_x_2
                mstore(0x1660, 0x090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b) // g2_y_1
                mstore(0x1680, 0x12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa) // g2_y_2
                mstore(0x16a0, 0x186282957db913abd99f91db59fe69922e95040603ef44c0bd7aa3adeef8f5ac) // neg_s_g2_x_1
                mstore(0x16c0, 0x17944351223333f260ddc3b4af45191b856689eda9eab5cbcddbbe570ce860d2) // neg_s_g2_x_2
                mstore(0x16e0, 0x06d971ff4a7467c3ec596ed6efc674572e32fd6f52b721f97e35b0b3d3546753) // neg_s_g2_y_1
                mstore(0x1700, 0x06ecdb9f9567f59ed2eee36e1e1d58797fd13cc97fafc2910f5e8a12f202fa9a) // neg_s_g2_y_2
                mstore(0x1720, 0x11799f9ff63344e62835bc043e0316a8329076f482c3f008a32cdc8c7fde1e67) // fixed_comms[0].x
                mstore(0x1740, 0x031477be4855c67620f75076bc2e83fb4e3bacb20cd50e19a83536c2b5daa7c3) // fixed_comms[0].y
                mstore(0x1760, 0x18beb969dccc1ae964cf7f9d994681399ce3fd93e9e8f788da43307b628da3dc) // fixed_comms[1].x
                mstore(0x1780, 0x2087b712d2fdcd9c8db075d6d640fcb4c17b91900d0f883ecf01792473221cdc) // fixed_comms[1].y
                mstore(0x17a0, 0x24088d69ddadddfb205393632f8cf1fe11bdf533332d9dda8b91c082b19d8150) // fixed_comms[2].x
                mstore(0x17c0, 0x1f1e11bf7dff7c9127e5d98e66fd076de7b21e781a6017d6d5202ed39501d6f9) // fixed_comms[2].y
                mstore(0x17e0, 0x1e12b29685b9f136f4d8d33f33719296ef6fd549c82896c63eb440c775e878c0) // fixed_comms[3].x
                mstore(0x1800, 0x2ad433a71a3696fa8d74999c090c50b09c5056aedd13cbe73df64fb411ca1112) // fixed_comms[3].y
                mstore(0x1820, 0x1e12b29685b9f136f4d8d33f33719296ef6fd549c82896c63eb440c775e878c0) // fixed_comms[4].x
                mstore(0x1840, 0x2ad433a71a3696fa8d74999c090c50b09c5056aedd13cbe73df64fb411ca1112) // fixed_comms[4].y
                mstore(0x1860, 0x2e39472b832414cda56ff3412b6eead14c721cc1f282963f3d7eee1a4e183732) // fixed_comms[5].x
                mstore(0x1880, 0x0c1495741f07d3749b9bfd01095cbe6af9c64484973e17a203b5a14fda708295) // fixed_comms[5].y
                mstore(0x18a0, 0x2e39472b832414cda56ff3412b6eead14c721cc1f282963f3d7eee1a4e183732) // fixed_comms[6].x
                mstore(0x18c0, 0x0c1495741f07d3749b9bfd01095cbe6af9c64484973e17a203b5a14fda708295) // fixed_comms[6].y
                mstore(0x18e0, 0x1f8ffa244c58f4e8516ec745766e824c1ca7da565a60c7b9227b1746ba59ed0c) // fixed_comms[7].x
                mstore(0x1900, 0x27d44767ed6a3f9252edb7767470064d04dcee9608a018979395a18f2b75a565) // fixed_comms[7].y
                mstore(0x1920, 0x1f8ffa244c58f4e8516ec745766e824c1ca7da565a60c7b9227b1746ba59ed0c) // fixed_comms[8].x
                mstore(0x1940, 0x27d44767ed6a3f9252edb7767470064d04dcee9608a018979395a18f2b75a565) // fixed_comms[8].y
                mstore(0x1960, 0x04391d013c0b6240b86196d8b85b9c13ab1ae3446b3dfa953455772210e3f0cf) // fixed_comms[9].x
                mstore(0x1980, 0x1d3bcac09b159c57f61ea1d39a0ea67b9041a209d501fe4d14a30d0f0bfc85e7) // fixed_comms[9].y
                mstore(0x19a0, 0x04391d013c0b6240b86196d8b85b9c13ab1ae3446b3dfa953455772210e3f0cf) // fixed_comms[10].x
                mstore(0x19c0, 0x1d3bcac09b159c57f61ea1d39a0ea67b9041a209d501fe4d14a30d0f0bfc85e7) // fixed_comms[10].y
                mstore(0x19e0, 0x1a60409e0190ab2bad50207ba423e640442cb42e36f89365a2c537d8c557bd3d) // fixed_comms[11].x
                mstore(0x1a00, 0x053cc370b98ee9d74b13197d23351b81bad65661715f96d428a1c42607ea850a) // fixed_comms[11].y
                mstore(0x1a20, 0x0938544327164c208d1eef8e03d80ad7c54fd288099c46b1dee91d46073824e0) // fixed_comms[12].x
                mstore(0x1a40, 0x078230f2764af42b1056f10797da733dbd416fdb36ede73ce58e7260fbce42bc) // fixed_comms[12].y
                mstore(0x1a60, 0x0cd438d8953763805de51454d6dc43aa30bd965d393436ab8dd1c7549136a711) // fixed_comms[13].x
                mstore(0x1a80, 0x12e73ffb495e3dddfb571dcdf9f10962581bad2032708c26ed2df8596ddba379) // fixed_comms[13].y
                mstore(0x1aa0, 0x29a6b218baa77ae4f7426b627a177e53c71164bb688b738484ce7ed882bc7e7c) // fixed_comms[14].x
                mstore(0x1ac0, 0x073e950d236e06c578d1f1b1608704ce1870b0cfe890d28af655a8b8cb702c3b) // fixed_comms[14].y
                mstore(0x1ae0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].x
                mstore(0x1b00, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].y
                mstore(0x1b20, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[16].x
                mstore(0x1b40, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[16].y
                mstore(0x1b60, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].x
                mstore(0x1b80, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].y
                mstore(0x1ba0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[18].x
                mstore(0x1bc0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[18].y
                mstore(0x1be0, 0x0cb6e6c753a08448f51c29282d2307eded1babf821c4b0817ec14b9276d65dca) // fixed_comms[19].x
                mstore(0x1c00, 0x1151836bb66cce12a29bebda427e462c66461d7ecd9552184cc2d6f5c6ba3245) // fixed_comms[19].y
                mstore(0x1c20, 0x0cb6e6c753a08448f51c29282d2307eded1babf821c4b0817ec14b9276d65dca) // fixed_comms[20].x
                mstore(0x1c40, 0x1151836bb66cce12a29bebda427e462c66461d7ecd9552184cc2d6f5c6ba3245) // fixed_comms[20].y
                mstore(0x1c60, 0x1bdb9c244bf30cb9f650cbf9a6e339aab9da6d24b80a2ce97b1ba88322e02578) // fixed_comms[21].x
                mstore(0x1c80, 0x2c0710d4e33c14d8f73ad61c71b17845f33a79d576f6298c166cf04cfbfcc86c) // fixed_comms[21].y
                mstore(0x1ca0, 0x1bdb9c244bf30cb9f650cbf9a6e339aab9da6d24b80a2ce97b1ba88322e02578) // fixed_comms[22].x
                mstore(0x1cc0, 0x2c0710d4e33c14d8f73ad61c71b17845f33a79d576f6298c166cf04cfbfcc86c) // fixed_comms[22].y
                mstore(0x1ce0, 0x135b81c8886effcf3b446d4ec69c30b111aae2e3de2ae52e95fddd0c5a786f05) // fixed_comms[23].x
                mstore(0x1d00, 0x2e862da95edb1eb1da6752ee10f7e516324da12746afb3de939b6053c60073f3) // fixed_comms[23].y
                mstore(0x1d20, 0x0faaae498c579fa1fa6aa58c7b6facac8fadcc4b59013b4935b1fd18c5f48053) // fixed_comms[24].x
                mstore(0x1d40, 0x1ae8e48fa21ebf051a75ded9bda021c01d67616ef99ff3375e003e1c4a6e3cfc) // fixed_comms[24].y
                mstore(0x1d60, 0x0aa07118db22907b5b336106f324d8fa60c126d3a2b2e17d4b6708cf51a3d3ba) // fixed_comms[25].x
                mstore(0x1d80, 0x26b6c163eaba846e3af74011d7b96c24bc30b13d6937ee07808535b0b154748b) // fixed_comms[25].y
                mstore(0x1da0, 0x15fccd4a7cb54fc3ac0f18bcded0f1860db4a374b5a99820c8ab811eace5896b) // fixed_comms[26].x
                mstore(0x1dc0, 0x03f8e50bd6b4602e9f4edfb0e56b0bd891bf074150a2e7fb83aa8cbce5382665) // fixed_comms[26].y
                mstore(0x1de0, 0x0abbf12e39fff60750c5a262fd0e8276787809a17eb8725689c4fce6703a2cb4) // fixed_comms[27].x
                mstore(0x1e00, 0x2f11bca5d9ed2b220cb4810948ea3a1900027ff0a5707f99dcec367db10afd4b) // fixed_comms[27].y
                mstore(0x1e20, 0x0abbf12e39fff60750c5a262fd0e8276787809a17eb8725689c4fce6703a2cb4) // fixed_comms[28].x
                mstore(0x1e40, 0x2f11bca5d9ed2b220cb4810948ea3a1900027ff0a5707f99dcec367db10afd4b) // fixed_comms[28].y
                mstore(0x1e60, 0x18dd88f0a59e1bf9ce90660b73ff87a4acb63d3ee803eafedbfa6fd6beac7d27) // fixed_comms[29].x
                mstore(0x1e80, 0x29951eb41c920ff797c59cd9f0a298b8460fda0f82b7c25548fb73a45fd83aee) // fixed_comms[29].y
                mstore(0x1ea0, 0x18dd88f0a59e1bf9ce90660b73ff87a4acb63d3ee803eafedbfa6fd6beac7d27) // fixed_comms[30].x
                mstore(0x1ec0, 0x29951eb41c920ff797c59cd9f0a298b8460fda0f82b7c25548fb73a45fd83aee) // fixed_comms[30].y
                mstore(0x1ee0, 0x1d78ccbcc5542426af5d1ca2ce8068cafc3f36f9aea3cc0f3e2013b8d8da36e3) // fixed_comms[31].x
                mstore(0x1f00, 0x2635ccc10c5bb6935d6de727c64c06bb86ff29eec6777a0e1d2443cca9450aff) // fixed_comms[31].y
                mstore(0x1f20, 0x1d78ccbcc5542426af5d1ca2ce8068cafc3f36f9aea3cc0f3e2013b8d8da36e3) // fixed_comms[32].x
                mstore(0x1f40, 0x2635ccc10c5bb6935d6de727c64c06bb86ff29eec6777a0e1d2443cca9450aff) // fixed_comms[32].y
                mstore(0x1f60, 0x00207e41ab5fdc1138f0d85f5a8f0cafb170d6e5045d48c090c1c1506e9fda4e) // fixed_comms[33].x
                mstore(0x1f80, 0x0923eec076230b988260b2b70ffe310d4334abb8f4abe3907738eeb24cf7c8cb) // fixed_comms[33].y
                mstore(0x1fa0, 0x00207e41ab5fdc1138f0d85f5a8f0cafb170d6e5045d48c090c1c1506e9fda4e) // fixed_comms[34].x
                mstore(0x1fc0, 0x0923eec076230b988260b2b70ffe310d4334abb8f4abe3907738eeb24cf7c8cb) // fixed_comms[34].y
                mstore(0x1fe0, 0x2c216e5361ee2b91c7566bf2a376ba65e4bbca308dd8922723dbfcef1d472bdb) // fixed_comms[35].x
                mstore(0x2000, 0x14c592aabb225488918b5fc2d62e932c605cea9d12e0d6c71d50e2191ea8fcef) // fixed_comms[35].y
                mstore(0x2020, 0x2c216e5361ee2b91c7566bf2a376ba65e4bbca308dd8922723dbfcef1d472bdb) // fixed_comms[36].x
                mstore(0x2040, 0x14c592aabb225488918b5fc2d62e932c605cea9d12e0d6c71d50e2191ea8fcef) // fixed_comms[36].y
                mstore(0x2060, 0x1931c5ec798ac8bff8afdcf546bc87bb97179f4aa338730bc7a4e6a9c026dcea) // fixed_comms[37].x
                mstore(0x2080, 0x285a6baf5146b1c64723d4e0a62be56a7917aa394fce35125be3d5ddc1c84c54) // fixed_comms[37].y
                mstore(0x20a0, 0x1931c5ec798ac8bff8afdcf546bc87bb97179f4aa338730bc7a4e6a9c026dcea) // fixed_comms[38].x
                mstore(0x20c0, 0x285a6baf5146b1c64723d4e0a62be56a7917aa394fce35125be3d5ddc1c84c54) // fixed_comms[38].y
                mstore(0x20e0, 0x22c5e6c88a0047cb36dfb2ef84add063788e8f2aea8a19f741a96ceca663a041) // fixed_comms[39].x
                mstore(0x2100, 0x28bdd92e05b637a2822585b58d5256d95f495c99f8131bb387097a49c0942984) // fixed_comms[39].y
                mstore(0x2120, 0x22c5e6c88a0047cb36dfb2ef84add063788e8f2aea8a19f741a96ceca663a041) // fixed_comms[40].x
                mstore(0x2140, 0x28bdd92e05b637a2822585b58d5256d95f495c99f8131bb387097a49c0942984) // fixed_comms[40].y
                mstore(0x2160, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[41].x
                mstore(0x2180, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[41].y
                mstore(0x21a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[42].x
                mstore(0x21c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[42].y
                mstore(0x21e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[43].x
                mstore(0x2200, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[43].y
                mstore(0x2220, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[44].x
                mstore(0x2240, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[44].y
                mstore(0x2260, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[45].x
                mstore(0x2280, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[45].y
                mstore(0x22a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[46].x
                mstore(0x22c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[46].y
                mstore(0x22e0, 0x0441290a56797630ffb8d04eceb4ab209e88d88a54f0046e2fa3344cfde37cf5) // fixed_comms[47].x
                mstore(0x2300, 0x1b135cc67dd787d346db753a1dcfadc8d940c5d01e9179a48838992074680c22) // fixed_comms[47].y
                mstore(0x2320, 0x0441290a56797630ffb8d04eceb4ab209e88d88a54f0046e2fa3344cfde37cf5) // fixed_comms[48].x
                mstore(0x2340, 0x1b135cc67dd787d346db753a1dcfadc8d940c5d01e9179a48838992074680c22) // fixed_comms[48].y
                mstore(0x2360, 0x2b9cbda9626cb93b0b676514e02dae623c9eb155dd7d63aba92c850b8de4608f) // fixed_comms[49].x
                mstore(0x2380, 0x12e93edc188abb3d1cabb633b16694d140c49d279c154642530702f05581e293) // fixed_comms[49].y
                mstore(0x23a0, 0x2b9cbda9626cb93b0b676514e02dae623c9eb155dd7d63aba92c850b8de4608f) // fixed_comms[50].x
                mstore(0x23c0, 0x12e93edc188abb3d1cabb633b16694d140c49d279c154642530702f05581e293) // fixed_comms[50].y
                mstore(0x23e0, 0x0dd8efbfbff77e73e95c52405e34e21b49ace01a538ce7c7dab6e296035dfd12) // fixed_comms[51].x
                mstore(0x2400, 0x2c1d266fcd40e2d3c2938f097607c077b0327a80e43337f7c5766e602e7b50b3) // fixed_comms[51].y
                mstore(0x2420, 0x0dd8efbfbff77e73e95c52405e34e21b49ace01a538ce7c7dab6e296035dfd12) // fixed_comms[52].x
                mstore(0x2440, 0x2c1d266fcd40e2d3c2938f097607c077b0327a80e43337f7c5766e602e7b50b3) // fixed_comms[52].y
                mstore(0x2460, 0x0b6468808ce21ef237c343c2d1f572bffa9f6389b89b94d1b4e99ba0e8a6d0d1) // fixed_comms[53].x
                mstore(0x2480, 0x000e075227060ebe5d71b8b29518fecf6638fcc8d4056566fc33a79188168344) // fixed_comms[53].y
                mstore(0x24a0, 0x0b6468808ce21ef237c343c2d1f572bffa9f6389b89b94d1b4e99ba0e8a6d0d1) // fixed_comms[54].x
                mstore(0x24c0, 0x000e075227060ebe5d71b8b29518fecf6638fcc8d4056566fc33a79188168344) // fixed_comms[54].y
                mstore(0x24e0, 0x1985fe3d09b12b9c5bcbdc33aa37137e3275eb8c4204074968ac629f81401b3e) // fixed_comms[55].x
                mstore(0x2500, 0x25ea5b000245c0839fee030a53381edb42ef5566c79473b182e97caa59316a9e) // fixed_comms[55].y
                mstore(0x2520, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[56].x
                mstore(0x2540, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[56].y
                mstore(0x2560, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[57].x
                mstore(0x2580, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[57].y
                mstore(0x25a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[58].x
                mstore(0x25c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[58].y
                mstore(0x25e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[59].x
                mstore(0x2600, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[59].y
                mstore(0x2620, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[60].x
                mstore(0x2640, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[60].y
                mstore(0x2660, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[61].x
                mstore(0x2680, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[61].y
                mstore(0x26a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[62].x
                mstore(0x26c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[62].y
                mstore(0x26e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[63].x
                mstore(0x2700, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[63].y
                mstore(0x2720, 0x2f638fb9eb23e8c98127a6aad5eda89afb25b70ee3b63e5a860e124070ecc21b) // fixed_comms[64].x
                mstore(0x2740, 0x02e5ed61223cbcc48818b9fdedb3b1b178f542336585c900c47de695b27bee68) // fixed_comms[64].y
                mstore(0x2760, 0x2f638fb9eb23e8c98127a6aad5eda89afb25b70ee3b63e5a860e124070ecc21b) // fixed_comms[65].x
                mstore(0x2780, 0x02e5ed61223cbcc48818b9fdedb3b1b178f542336585c900c47de695b27bee68) // fixed_comms[65].y
                mstore(0x27a0, 0x0e56f033f15404426e48e4ed31751a98db9e27f273f30418ee6baf4306cce3b5) // fixed_comms[66].x
                mstore(0x27c0, 0x273d24d04e42b94d92983c4bbb7412cbc7aced54e864c0fdf87f657abf7a0bda) // fixed_comms[66].y
                mstore(0x27e0, 0x0e56f033f15404426e48e4ed31751a98db9e27f273f30418ee6baf4306cce3b5) // fixed_comms[67].x
                mstore(0x2800, 0x273d24d04e42b94d92983c4bbb7412cbc7aced54e864c0fdf87f657abf7a0bda) // fixed_comms[67].y
                mstore(0x2820, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[68].x
                mstore(0x2840, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[68].y
                mstore(0x2860, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[69].x
                mstore(0x2880, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[69].y
                mstore(0x28a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[70].x
                mstore(0x28c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[70].y
                mstore(0x28e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[71].x
                mstore(0x2900, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[71].y
                mstore(0x2920, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[72].x
                mstore(0x2940, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[72].y
                mstore(0x2960, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[73].x
                mstore(0x2980, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[73].y
                mstore(0x29a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[74].x
                mstore(0x29c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[74].y
                mstore(0x29e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[75].x
                mstore(0x2a00, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[75].y
                mstore(0x2a20, 0x2dd1473f00a2ef16a8628354e7f9f57c5271c83249db3990097f3a4722a40f37) // fixed_comms[76].x
                mstore(0x2a40, 0x02fcc4533045979b076038b54dd04e93aec32e0cf391885bf01216b7a02592e9) // fixed_comms[76].y
                mstore(0x2a60, 0x2dd1473f00a2ef16a8628354e7f9f57c5271c83249db3990097f3a4722a40f37) // fixed_comms[77].x
                mstore(0x2a80, 0x02fcc4533045979b076038b54dd04e93aec32e0cf391885bf01216b7a02592e9) // fixed_comms[77].y
                mstore(0x2aa0, 0x25b85c14a2d5dda1d94183155d5c38d976f7b20a96772d1bed78a337adf2cd94) // fixed_comms[78].x
                mstore(0x2ac0, 0x20f833b24cf05ea59ef4567c3cb3e5588ddea2bcab8d72081f6c428ea07c6149) // fixed_comms[78].y
                mstore(0x2ae0, 0x25b85c14a2d5dda1d94183155d5c38d976f7b20a96772d1bed78a337adf2cd94) // fixed_comms[79].x
                mstore(0x2b00, 0x20f833b24cf05ea59ef4567c3cb3e5588ddea2bcab8d72081f6c428ea07c6149) // fixed_comms[79].y
                mstore(0x2b20, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[80].x
                mstore(0x2b40, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[80].y
                mstore(0x2b60, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[81].x
                mstore(0x2b80, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[81].y
                mstore(0x2ba0, 0x2f291f65797a38aa75e4f5dcf1dd1fe80349d65f9dfff20d5af43919c4950399) // fixed_comms[82].x
                mstore(0x2bc0, 0x0a93b6f651ff5739ae8f20f2b8bc69a8f54f510f72e77a758aa97930093bad9f) // fixed_comms[82].y
                mstore(0x2be0, 0x2fd3dc0c4b4d870c547bbc2779322a3247dad0175a7ff72b63b6835abaab3de1) // fixed_comms[83].x
                mstore(0x2c00, 0x0abec2da0ef80a8739332898ff1122e105188d1a44930f18ae4dba766d40f6c4) // fixed_comms[83].y
                mstore(0x2c20, 0x271108a7797999da577a7069568d3677dee375222f63a28c9d81d88c30e8b2b5) // fixed_comms[84].x
                mstore(0x2c40, 0x26743f8733eaff0cb77189127ca160313febcac3ddb41dc9f24fb33560e08cc9) // fixed_comms[84].y
                mstore(0x2c60, 0x1528055f19fc5aa598b710ae872c5e537c61c23145c4bb692ea99e3aa2245a07) // fixed_comms[85].x
                mstore(0x2c80, 0x11b1db695bc3e056c05d35081bb57cc7183efc5bef685d88dc37d0de4b304150) // fixed_comms[85].y
                mstore(0x2ca0, 0x299db42d6ec67e5a3f74876c5e38b3b1c0efff0b5eac261b0c4ee8918f967732) // fixed_comms[86].x
                mstore(0x2cc0, 0x1eb2ae6ee9fa72121a6edd3ca65fcf3c4f84b26c1fed2dd71af02ac34f0ae7b1) // fixed_comms[86].y
                mstore(0x2ce0, 0x299db42d6ec67e5a3f74876c5e38b3b1c0efff0b5eac261b0c4ee8918f967732) // fixed_comms[87].x
                mstore(0x2d00, 0x1eb2ae6ee9fa72121a6edd3ca65fcf3c4f84b26c1fed2dd71af02ac34f0ae7b1) // fixed_comms[87].y
                mstore(0x2d20, 0x0b10619ae188107c459a5650772f76d97573300d5dde3f146526b1a4fbdc88e3) // fixed_comms[88].x
                mstore(0x2d40, 0x08e01d6773c471acdba18e3820b74af236e57e4e3ecc75abc1dc5bad50eedfde) // fixed_comms[88].y
                mstore(0x2d60, 0x0b10619ae188107c459a5650772f76d97573300d5dde3f146526b1a4fbdc88e3) // fixed_comms[89].x
                mstore(0x2d80, 0x08e01d6773c471acdba18e3820b74af236e57e4e3ecc75abc1dc5bad50eedfde) // fixed_comms[89].y
                mstore(0x2da0, 0x0092243dbb8bf8f1acaf6b2bc25e15583149ed8b86d2ca9a5334a8b8b662bd5e) // fixed_comms[90].x
                mstore(0x2dc0, 0x20e3a10adb64b70ca710cfa3e248b47154171cf53ce2deb95349e541032d39cf) // fixed_comms[90].y
                mstore(0x2de0, 0x0ee52f6f36b61bd39cf740e10885060f594561a220425db3fcb25d31c33520c2) // fixed_comms[91].x
                mstore(0x2e00, 0x2d1dc7196693f63ac616e4a0f737d000f9893578b4fc5d303dd240e521d759ed) // fixed_comms[91].y
                mstore(0x2e20, 0x1a640c7ff1ea13cfad0c121280504946158c354a111f25ad94170bc7667f79ee) // fixed_comms[92].x
                mstore(0x2e40, 0x03b0eee970bdb7dba72d8bd301107b9346ebb0b87fdb2c8d358f1e528439fff5) // fixed_comms[92].y
                mstore(0x2e60, 0x2146efc5b66fdaeebdbf090044097fa279ac1027c1605fde1edae4d4b863d188) // fixed_comms[93].x
                mstore(0x2e80, 0x1a83706a969edbb0bf837ddd1d85def2ac020d578a5f475ed1ac19f7c3e3a710) // fixed_comms[93].y
                mstore(0x2ea0, 0x014266d844d68c1b097691c02421c204cd9de9c53effe3a63cfb324c5b2d8a88) // fixed_comms[94].x
                mstore(0x2ec0, 0x2d27259b74708e0e00de02aae7064393d9619221b92bdb130d730e94acb9422d) // fixed_comms[94].y
                mstore(0x2ee0, 0x27fc61f478c9ab98725cc641fdfed9745efbb4a82e759cd688780dd5d658dde5) // fixed_comms[95].x
                mstore(0x2f00, 0x1132295eca80f5e4561abc05fcf98ec33a3fe5fd25bcb9bed574e783529339a8) // fixed_comms[95].y
                mstore(0x2f20, 0x07fb595ed7db847580ea79a5e2c18c32f5e2d8794af9f37cad1256ba79034b53) // fixed_comms[96].x
                mstore(0x2f40, 0x2b2d05068133f53ac245409b35534530988131c87ce6f637c6de3e5df4897cb7) // fixed_comms[96].y
                mstore(0x2f60, 0x0245688e52c81040735b4a3de7aaea94c81e3086ef726fad3fd144a757ed2090) // fixed_comms[97].x
                mstore(0x2f80, 0x19f3029e8addaa23a386caf8a6151308cddb4e822c8deb7234bcf336271b6c9a) // fixed_comms[97].y
                mstore(0x2fa0, 0x0a1713fa2ffe79c8be06e277a764d6e3397aa8b0402362c0f3a24eac0b8e7d7c) // fixed_comms[98].x
                mstore(0x2fc0, 0x253006535470d8aaf5b94dfb3a71aaf9c68979f4fc1e6dacb930f7105e83069a) // fixed_comms[98].y
                mstore(0x2fe0, 0x189e4672419480c5edf7a5ec87baa393c539ca2e60ef8f989e537c0c9f437770) // fixed_comms[99].x
                mstore(0x3000, 0x25f5b4ea13372683c670e1910e91d7c211cbe8a90157b0de669f57608d41f2cc) // fixed_comms[99].y
                mstore(0x3020, 0x2f59d560128176d9133cb5a6b3c27aea04a54bcff6a6ceb9f2ae85af9cc2d326) // fixed_comms[100].x
                mstore(0x3040, 0x268eee46270c6e498a7473d7215ab4321160dc3a88da81e1f1d3a0195fd17474) // fixed_comms[100].y
                mstore(0x3060, 0x19f49dff2199f8a6407fd6d0b83b0e6996ed7784701b502134827fdf8060f809) // fixed_comms[101].x
                mstore(0x3080, 0x1dd8bbf2fb6cba4fb765d008f1d37677541d5e357554c7f59cf03987b1202e15) // fixed_comms[101].y
                mstore(0x30a0, 0x08126cb4858d8a248c1129ff1d26b86818a087abe732e431e0f7ce19250a3fbe) // fixed_comms[102].x
                mstore(0x30c0, 0x167ee87da03bb301446bd8e6000ca147cd86e643f9b895412b6cdb13270011da) // fixed_comms[102].y
                mstore(0x30e0, 0x107e7b8a57238b692bc1e8e138046b897c1a2fcad6f50d1ce04f9209a427ba00) // fixed_comms[103].x
                mstore(0x3100, 0x036642a41ca7cbc183cbf891e1bcdaf4f4131b02eef67ee9d0d638809cabbb92) // fixed_comms[103].y
                mstore(0x3120, 0x1b349cef04ef85560e3efebb9ac379550968786b0d03a6ee7be5b29f78a809ce) // fixed_comms[104].x
                mstore(0x3140, 0x1bb9e534ec3f82567240a7659d6b228961624089348c342d47cc8a0471df41c5) // fixed_comms[104].y
                mstore(0x3160, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[105].x
                mstore(0x3180, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[105].y
                mstore(0x31a0, 0x3001a324ff4fc0dcb5572bc022842c2e204755a188acce24231abeeb0e1dca81) // fixed_comms[106].x
                mstore(0x31c0, 0x21d89af48b7ebb2dbde2bcb4d3dc40229e1b96b117ac607c8e56ec4afb14d6b6) // fixed_comms[106].y
                mstore(0x31e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[107].x
                mstore(0x3200, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[107].y
                mstore(0x3220, 0x106382b0cfc3b031e98372d0ec00c2ab621d0130c739cfe629663a7ac4d19b86) // fixed_comms[108].x
                mstore(0x3240, 0x2b55514dcbdb1f854e142d4707868f58d581cb1586427bacae8a833fe578ecee) // fixed_comms[108].y
                mstore(0x3260, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[109].x
                mstore(0x3280, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[109].y
                mstore(0x32a0, 0x156dfb123922264c0dd0be92dfeb3c6b9347869c73a70e97002a556819d844af) // fixed_comms[110].x
                mstore(0x32c0, 0x1c637cfaa9038e18bd994c3043da094b3074077893a8dc2fb787f282dc30cb2c) // fixed_comms[110].y
                mstore(0x32e0, 0x282ddd184fa6d4a509e6c5d2969db38aca453747ac7317af22bf429c51e6e9ed) // fixed_comms[111].x
                mstore(0x3300, 0x21f99749dc51b8d5c5bd01a31a72b3fceb585436bdd95664a805bc46bad1799c) // fixed_comms[111].y
                mstore(0x3320, 0x2a323c142947f03f7361c09afdeaef3c3f0528dbbf043a93ba216c5b6dac0a37) // fixed_comms[112].x
                mstore(0x3340, 0x1600b9e99c273db9b07834749ca95d7cd05d9c2353f4e987c264f00ded9cb85d) // fixed_comms[112].y
                mstore(0x3360, 0x147b595f357ba9e4ea29ecd99705ef27632762414a992e6af9164d95e8424136) // fixed_comms[113].x
                mstore(0x3380, 0x28484afc821be8525aaed343c7d0c69be03d1e9cbc2a9fa5d40e30d0f749df9b) // fixed_comms[113].y
                mstore(0x33a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[114].x
                mstore(0x33c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[114].y
                mstore(0x33e0, 0x0387635d7c60c5d47d6ea4657528b74fca4ff70da2c1cc00f98099868de9e654) // fixed_comms[115].x
                mstore(0x3400, 0x14db41a07fce24fa833b24e150ce9b2a5e12e7787ea094193212c6b16b0fd38e) // fixed_comms[115].y
                mstore(0x3420, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[116].x
                mstore(0x3440, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[116].y
                mstore(0x3460, 0x259cd9d5dd3166f46988936ec8c217cbf3b5812616e33e8f86413b81d82c67dc) // fixed_comms[117].x
                mstore(0x3480, 0x266e5e033692a0dccf94034dbd1fd51c4970517d7ddc5b8096d87bcb1a63bb3a) // fixed_comms[117].y
                mstore(0x34a0, 0x0a46bde2ad26d76799f4505fc428139fb27cd892658713f4a9f08b5b557e1126) // fixed_comms[118].x
                mstore(0x34c0, 0x0ef6c98e31892df664e7164c05cfa81a91e67c84b707f709ccac13983c25dcfa) // fixed_comms[118].y
                mstore(0x34e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[119].x
                mstore(0x3500, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[119].y
                mstore(0x3520, 0x0ede26a46e0dc1ff2019428e39828d04f6ab45472b00ba2d0fb3d1bcbcfd48be) // fixed_comms[120].x
                mstore(0x3540, 0x2f79960003aca9e735b343960d5eb1939de5cf0ac5d463131fb1e97d71b79312) // fixed_comms[120].y
                mstore(0x3560, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[121].x
                mstore(0x3580, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[121].y
                mstore(0x35a0, 0x022544f49847ec003e3745c6e17bd5953e0d71229d0a1217cb347caeb08f66d8) // fixed_comms[122].x
                mstore(0x35c0, 0x2c3512762205f5fe081a8b5e60565e7c031a97dd82befab407d34dd2bbbae166) // fixed_comms[122].y
                mstore(0x35e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[123].x
                mstore(0x3600, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[123].y
                mstore(0x3620, 0x1e7239bc99e8584665d5fb230cd069f5faf7be9eac123a7e1acd2de6e4c0ab7d) // permutation_comms[0].x
                mstore(0x3640, 0x261f00fa80c15889d0500d59c4f19fd0cb89ca32c1f862ee322a4f5ae56ec16e) // permutation_comms[0].y
                mstore(0x3660, 0x010604c19ce1549576367be789ae0a069285622550c28aa685e1b08b25bb386b) // permutation_comms[1].x
                mstore(0x3680, 0x2290f048e32a57770f2f54fb01767816c631120054e762d33d6a357b10874e63) // permutation_comms[1].y
                mstore(0x36a0, 0x0772d3f0c3db8cc0cd270af45cac49536bea1eaf3932e340a74c7194fedfe1d8) // permutation_comms[2].x
                mstore(0x36c0, 0x11cd7762e9b6cec894f3cb1c6b84a1c950420135effa1df337bad950eb07dba0) // permutation_comms[2].y
                mstore(0x36e0, 0x2e6f04c747c688a97bd0179284499eeeb001e4c19a500fe3cedf9514d025f9ee) // permutation_comms[3].x
                mstore(0x3700, 0x1f038dd8ef7fafd60a6b6357120ca0186bb34ad50d2aff44973cde1b364d7c04) // permutation_comms[3].y
                mstore(0x3720, 0x2a048dc396e74ba370f2430b914c6df9fa471a15bf53494ce71b3c0350624f86) // permutation_comms[4].x
                mstore(0x3740, 0x02a0942a8a20f67c204344568c1ae2132bd6f54cdfd54ea4e83084e8ee230926) // permutation_comms[4].y
                mstore(0x3760, 0x2b7841b0aa6310e17c1694ec4405fb4732198f72b0dc149e2394974c8b18a5e4) // permutation_comms[5].x
                mstore(0x3780, 0x04c53dfae0147554ab4776938abf5be4e7906b2f0b008dd1cbd26a6324dad08c) // permutation_comms[5].y
                mstore(0x37a0, 0x29240f4d0bbc9c0cc48071366e8b15c6c1f30bb2870a3ff343622ce8792ce131) // permutation_comms[6].x
                mstore(0x37c0, 0x29a13994cfdc163fee73d0b9858ceb31d819f742bc4c45a09ed9019ca8570928) // permutation_comms[6].y
                mstore(0x37e0, 0x1e97d0daa4e415f90bdfffca91e58425826f84db11acab1447f147a902db149d) // permutation_comms[7].x
                mstore(0x3800, 0x261cb4f5c31ceb34c19ba7055e8b9efc23222e200711f7cac306e8038ce21cb4) // permutation_comms[7].y
                mstore(0x3820, 0x1e16a168876ad59f60bb1cd5f70bcf16c378ae57f5481c350aa7483e4148bbb4) // permutation_comms[8].x
                mstore(0x3840, 0x16e3411803daa446b0fa9193db7784fc5c7242fde98f676cb66b372ebd37e09c) // permutation_comms[8].y
                mstore(0x3860, 0x00ae4cc36e185f666d034dfb132b8f5a5861730b9d34316e15df1130196e57d4) // permutation_comms[9].x
                mstore(0x3880, 0x1e84382d43f6e8b4844ee9f4a0bb32323b116e97f40e00e0777916e9e30bc61d) // permutation_comms[9].y
                mstore(0x38a0, 0x27faad2fce750ae5ede44e1f1cd831a7093f3560da37c1be3d97acdd199deec5) // permutation_comms[10].x
                mstore(0x38c0, 0x0b3aba916a947140ec8b1c0e62bada2401963f8209d93dfc6dd72a842200dccc) // permutation_comms[10].y
                mstore(0x38e0, 0x183356b834e9c3f9039123079f5dc7419486064382ea3a6b05812d60fdc748a6) // permutation_comms[11].x
                mstore(0x3900, 0x2393b606d7c0ac0b002aa36a9084c3ffd97f77ebd7ab18e5c91ea88d210e1b57) // permutation_comms[11].y
                mstore(0x3920, 0x17a9318c81e115a949f80c2e75e468f6d67c7c3c35d6692f24abd79510d97588) // permutation_comms[12].x
                mstore(0x3940, 0x2fc007ad11a12c2457d0577b4571e9ff76200d5a99a89a9b70fe9f93dae96fa3) // permutation_comms[12].y
                mstore(0x3960, 0x0092c7b79c0c90e8f1962b1bfc828ccb34072a072fac4695dfa73d16f7633df6) // permutation_comms[13].x
                mstore(0x3980, 0x14e749c55a66c62040d48486284e1c9d7ca27bcd250329876d144431a2a23e18) // permutation_comms[13].y
                mstore(0x39a0, 0x22f31b62aba374adefa1bedd074f5d6b66253c004c93976d9a73770082e2b19b) // permutation_comms[14].x
                mstore(0x39c0, 0x124367785a8a9d06fbb4037fbbff2f03cc7578693f34da36d18e61c5054e114f) // permutation_comms[14].y
                mstore(0x39e0, 0x1133b7661873aec0ab5b4c24e4f0704f56edb907cd3300a2696d0444983b83ab) // permutation_comms[15].x
                mstore(0x3a00, 0x0829f8b325742b7bff6237e59771335773cde410dd30fe9714c583f951450896) // permutation_comms[15].y
                mstore(0x3a20, 0x275238d1dae9c5188ef5e88152825b142f432970896a06282cc688682a30ecda) // permutation_comms[16].x
                mstore(0x3a40, 0x21398e4244086a6747a59dacff60e3bb81624f6d7cf3be3c59ff09dc5ddcc99f) // permutation_comms[16].y
                mstore(0x3a60, 0x29c5f7fe038e7e51ae197267b1bce418f5d25e95f67d34817f2381f3369dbcc4) // permutation_comms[17].x
                mstore(0x3a80, 0x0f3d645383b59a0c70cf9059eae024818808f5334887ac65bb90a43d4dd6c85e) // permutation_comms[17].y
                mstore(0x3aa0, 0x05e5b08e9d19a8f32f9ad502c509fa46cb7bc38608b3574563f2dbf8436536ba) // permutation_comms[18].x
                mstore(0x3ac0, 0x110c258401c5c8cc779c5e32d0a22f514d59522bee61e065e220a2839ea32ae7) // permutation_comms[18].y
                mstore(0x3ae0, 0x1caff5bf56dca46a6ca621ae02dace799bae60a0a6d61377e58628b4e52d834d) // permutation_comms[19].x
                mstore(0x3b00, 0x24290d3bd3b4bb316a934937ee4bb3803bd0e032f10f9aaf4dfd48977cd856aa) // permutation_comms[19].y
                mstore(0x3b20, 0x1a08a62dcff5ead0a81a20a10c2800756fe28a03ce76a1906c308af8983e942b) // permutation_comms[20].x
                mstore(0x3b40, 0x18e86bbdee5b01fd43357342cd3dfc3d85c84082620fc5180c4134235be6fb3d) // permutation_comms[20].y
                mstore(0x3b60, 0x2dbab75bcd03be5426f0355e211e9a9027a01021ba9478c0b4a7ed41f255568a) // permutation_comms[21].x
                mstore(0x3b80, 0x235ee856f749c920e0e17ab3851c4d04753a24372d2a5fd97b96580afeea8845) // permutation_comms[21].y
                mstore(0x3ba0, 0x0748d51baceed39706987e0a1a101361a01b22981408131c8277225363239602) // permutation_comms[22].x
                mstore(0x3bc0, 0x1bac38e9c96dd2f11e6df81722caac133d617a36310a397760124415f8665b2c) // permutation_comms[22].y
                mstore(0x3be0, 0x0e26dd2dabbe5f254258a8fa3ddd21f72040b60c715e62a0f37d5ec3d8aa9fcb) // permutation_comms[23].x
                mstore(0x3c00, 0x2f5b01eda4ebc57e98c2dda9c644d28e1175240b8a187406eb4a7c6856aa7594) // permutation_comms[23].y
                mstore(0x3c20, 0x137399af964b634b89b407b8da68f67d094af5656887eb28426eae20f7ca47ce) // permutation_comms[24].x
                mstore(0x3c40, 0x0bbbfe3fae2e70c92a8fe1666fadb9ed1bfd7da2eb2bcfea4daaf9815e0a5edd) // permutation_comms[24].y
                mstore(0x3c60, 0x0d62a0bccc6fed2d3fa986c827b898a01bdf72047d27fbfd15cba1b7d3fe51f8) // permutation_comms[25].x
                mstore(0x3c80, 0x026d55182923fb59e6f9b4686782c4d69978bca4884b70772312984a7a77cf8f) // permutation_comms[25].y
                mstore(0x3ca0, 0x2f77faf77485894eae12173438c3a25c7553aa2146bc99a1db13f72eb99120db) // permutation_comms[26].x
                mstore(0x3cc0, 0x0b51d114dea7c63ee625ed1c98d8e6d8ce25275930b2a224940f61fa36046e87) // permutation_comms[26].y
                mstore(0x3ce0, 0x07338dd53bde3e76b75b8a79b02a8966527c97f5dab784da37d09222224c2f6c) // permutation_comms[27].x
                mstore(0x3d00, 0x01cbe0021ef889f7fd92639b5d3589bef532665a8a12b63dc6e594581bb0e0fc) // permutation_comms[27].y
                mstore(0x3d20, 0x2a8700724ec0ec8d9da2c3782559940f7ac0e8a116973140742194fee8709eb3) // permutation_comms[28].x
                mstore(0x3d40, 0x0526930e2e2e91355fafbaca278483efc37de0cc9978984a738c195b5cd1617c) // permutation_comms[28].y
                mstore(0x3d60, 0x27ba32bcd4a668af87946caacb7d79cba980aae19ff75a618ffee52638b4f028) // permutation_comms[29].x
                mstore(0x3d80, 0x2680e3515c64dba4ce19a121a6e0573c5e42112a36d973e8f924d7537af0112b) // permutation_comms[29].y
                mstore(0x3da0, 0x0d9dd11a4e9da4dbeec6a384adc1d38f5d4e9a30b23d728a8c8d2343ed9c8216) // permutation_comms[30].x
                mstore(0x3dc0, 0x1d5e162dcf33ad401663b026bcb8fb04712b916eb1717aa86fa790a420be2772) // permutation_comms[30].y
                mstore(0x3de0, 0x2c4a8872641bde14757285f050cd9749735c65a817ee8e04aeb438dbe3116207) // permutation_comms[31].x
                mstore(0x3e00, 0x228c2affb713293bd1bd0922267358d533c08dfa4f380e9970e9d3f3114c77fb) // permutation_comms[31].y
                mstore(0x3e20, 0x07b72b10d68b20f06990e5a460280f5e2f1d5700f4c46bb1ed8cf21249f1de26) // permutation_comms[32].x
                mstore(0x3e40, 0x21c9c44b2c8f77320510b09fd408eff5ce5177332d0a19a4bb143b0ec116b3f2) // permutation_comms[32].y
                mstore(0x3e60, 0x16873c316467d9a3994456c3575fafcffef834854dd94a7f105c96441a53cf7b) // permutation_comms[33].x
                mstore(0x3e80, 0x2fd2deec0da7375394621cff4bc2511277f3bab3a2c2f02b95b3923190ad674f) // permutation_comms[33].y
                mstore(0x3ea0, 0x0f5793a667e3edca173631b8abdef8022abf9073f892419efb9994534ff5abc0) // permutation_comms[34].x
                mstore(0x3ec0, 0x154ab54aea7f0dfe1607207774e0bcfe1b9cd2d77190c6359313b0a153833d04) // permutation_comms[34].y
                mstore(0x3ee0, 0x22603fd3fd92070b441b2c8ea1e8f5ad2c9f845ed6e26ae9d856180a2774ac58) // permutation_comms[35].x
                mstore(0x3f00, 0x18a493a09025b406d268066e9c4e61714554ab13e2108fffe219228f8179be2a) // permutation_comms[35].y
                mstore(0x3f20, 0x00ac7c2fabb9a352fd0abe05355c810ad1c46c36c8e852b94871024ce715b477) // permutation_comms[36].x
                mstore(0x3f40, 0x164b23f53dfdaf6db28a0c4c936f3bd860437dcb3a8dd366e79bdf076c109b44) // permutation_comms[36].y
                mstore(0x3f60, 0x0cfa81778c87be01d5f1360e16fc5be3896ce947a8dfe845f15ce6bbcbe902f0) // permutation_comms[37].x
                mstore(0x3f80, 0x2385d79488e5a22ff2f76db2c2b454bc041638617b5606e786a7c888a2e81986) // permutation_comms[37].y
                mstore(0x3fa0, 0x29001c69e33917fb9c18da2e4c359a9ccb0e93089524ceb41722ba0f91d225a1) // permutation_comms[38].x
                mstore(0x3fc0, 0x2fbb84a129c623e4be17779ddcdd43b2bdc22ab67a2ec0f2238530c32bda450d) // permutation_comms[38].y
                mstore(0x3fe0, 0x0748c617d4b52202332b5c46709d7a4e726d1dcf65c3238b648ccb1517e17e2e) // permutation_comms[39].x
                mstore(0x4000, 0x1e9d2230c3d62f41529e7f6522c3ba1b160d5f62a92615abc306ae3311f38090) // permutation_comms[39].y
                mstore(0x4020, 0x0030bb4143d4fa05d7051fdd07d80142175bc4166fa2849a0c465d1c2073badc) // permutation_comms[40].x
                mstore(0x4040, 0x068e54914d234231541e4c4d099bfaffe83cf150b28299e80fe63da61621b632) // permutation_comms[40].y
                mstore(0x4060, 0x1a3d4f3e5e0e7b8be9a3afc95223c63ec27407ba21e36972a88d35226963c3ef) // permutation_comms[41].x
                mstore(0x4080, 0x20e1933f1cc2fdcc2e1032c699b2321f2cdfe32887ac1129ace8638f3f37a3e9) // permutation_comms[41].y
                mstore(0x40a0, 0x063d78bd0d912dd2bee52114114a13f33065e8a2b16ed656db019a69ee85687d) // permutation_comms[42].x
                mstore(0x40c0, 0x08a4a9aac247a7ea1b489eda1608c81d6722628d557f6465a7afca9299cd909d) // permutation_comms[42].y
                mstore(0x40e0, 0x02e248e605a62cc27858c53a8ee8d1a9edeb431c09f96e0c2b9c49d5af6c7fff) // permutation_comms[43].x
                mstore(0x4100, 0x09ea5b86ab4f6a2b6cda6ca16c632cc1c62452f01d36ed06aa347007dcb518e5) // permutation_comms[43].y
                mstore(0x4120, 0x19bfb80c0d98e7b2a3c4619385634f51c6340962652336b4b162d8a171c126dc) // permutation_comms[44].x
                mstore(0x4140, 0x21d50b42298fb7d92b2270a10397ecad61ec97174de1e2b072c676dda1f127f3) // permutation_comms[44].y
                mstore(0x4160, 0x20ffe0306e0e401e20b63fcbc397cdd0d852d2b2c1f8c85c43d7bb84c470ddb5) // permutation_comms[45].x
                mstore(0x4180, 0x1867d8aa472349c81f2f67adbf4b1eb5886607a0239f0b05a14a4123f8080c13) // permutation_comms[45].y
                mstore(0x41a0, 0x022a081f3a13b943f4e106a1d2d93fec29df6c26f34b68756e7112d144c58e01) // permutation_comms[46].x
                mstore(0x41c0, 0x035de2f533f1142366dd8aa0f0ecaea1fc73c4a8c2bd34b6f317cee48e19e4c2) // permutation_comms[46].y
                mstore(0x41e0, 0x197cd2b915b77c2458074af3093ea504c114ee18c14ac3b8cc23435d72c29902) // permutation_comms[47].x
                mstore(0x4200, 0x0e5b08a3086c923a4eb78b9d5a0b67a1e9ac0c754583dbe83b4845e014a06523) // permutation_comms[47].y
                mstore(0x4220, 0x043583b50f2dc31643016300262475467fc559426f5cb282cc4105e29014eda9) // permutation_comms[48].x
                mstore(0x4240, 0x2c8423e68aa519ecb879c21b7f9b9f790da8b7ac0e8ae2d180ee7c14ac5663f7) // permutation_comms[48].y
                mstore(0x4260, 0x26d78ff0254ff04193831a61ee326514f3c113587cd040e9cc1e678a2cdbf81d) // permutation_comms[49].x
                mstore(0x4280, 0x0bc4ef564baa47325f2c1454fbf895fa33d4c6e43903d8fa48f35542dfcb89f2) // permutation_comms[49].y
                mstore(0x42a0, 0x2d94289c76f5904b6860a2b7daced9a970548601c5452b00aeb63ab8523408a4) // permutation_comms[50].x
                mstore(0x42c0, 0x29415190b5fb17abf941c1afe117ab02de98ad8909472c3a434ca40f60e5fe90) // permutation_comms[50].y
                mstore(0x42e0, 0x1455f98bd56e3e9d5c4d573cffce104a2d64516a1916899bef556c046b00cab0) // permutation_comms[51].x
                mstore(0x4300, 0x2ffd9dda2ce5ca1f40cd97ab6b3da3a6780cc1eb4e76a31e8b0a505c2e69e357) // permutation_comms[51].y
                mstore(0x4320, 0x1e35b82f5a7d23d1f1ad1d470b5100ef19b68892b0d8acf0178e04e7553902d1) // permutation_comms[52].x
                mstore(0x4340, 0x0f2e301898c9fcc81e71f2cdab66eb931b4632499b99011401a78cf291b88855) // permutation_comms[52].y
                mstore(0x4360, 0x0d2a60f16b7d1379afa0b12e3f807ed30212c1f7eecd12dab7ae24ed28b40e66) // permutation_comms[53].x
                mstore(0x4380, 0x1fb7ebf0a79d015f012f29b3471037be752a9b607af5e229ced5a49490ee1777) // permutation_comms[53].y
                mstore(0x43a0, 0x0375267f1f0c7b4bc1ac3177fce196193eff4680acd297cacb4986ef21a89f45) // permutation_comms[54].x
                mstore(0x43c0, 0x181c3478c23a4a14992913b03c217494aa098d9c69f7ead40838a973669ec97d) // permutation_comms[54].y
                mstore(0x43e0, 0x178958e56f03f5caa902599dea62262e6ae23f247cf17667811c376416314b17) // permutation_comms[55].x
                mstore(0x4400, 0x15c3420c9c1cdb720b5d8e28703fb742601a58a7518a6f235ab78b05395a7818) // permutation_comms[55].y
                mstore(0x4420, 0x15458c3709633e36223cff6e468932f875edc6ed6b2c4fe59fed7f827a3a69d7) // permutation_comms[56].x
                mstore(0x4440, 0x167682e694e74977b7ea80ea24d75c298ff43f1aa8c29c6422ed2445a7f453da) // permutation_comms[56].y
                mstore(0x4460, 0x0ca8dfd4f93580ea8b0f5a7f8e32f5208b77fafb7be53f393af198a6a8db826e) // permutation_comms[57].x
                mstore(0x4480, 0x0e47ebddb3a485b91adc6dabf3b51a60db018cb01407617d27075148898554ff) // permutation_comms[57].y
                mstore(0x44a0, 0x0d10ee56aa2ab4386bd8a0726046439d8be211ef045613aafe1354520c5a0a9d) // permutation_comms[58].x
                mstore(0x44c0, 0x02a10a8417853739b7307f9a530ae7d966dcc77bad4b73e365332c392f75b515) // permutation_comms[58].y
                mstore(0x44e0, 0x07ec9b462f5397dd2c9dd682aedbfc5d48092af374badf6f7b29eaa5552ab66a) // permutation_comms[59].x
                mstore(0x4500, 0x16b3dc0906845951f943be964fcf22b01dd456e7519a41d60d69839d37b3d614) // permutation_comms[59].y
                mstore(0x4520, 0x2b5b23c6575cdd8097c2fe941655b8d24a87a012ae5e12f25d5369bd23856d0d) // permutation_comms[60].x
                mstore(0x4540, 0x2ed4db54eec23d36c4b39df0672c0460809880119417f35214f2f75c9faa732d) // permutation_comms[60].y
                mstore(0x4560, 0x06d12dbad683e423ac2f2f3fe005a52d04e9f86887040f71d03d4d47c96ea4a0) // permutation_comms[61].x
                mstore(0x4580, 0x2ce5a5ded5d7dc3e727e2a0bae5be967140d436d6d1a3c6f76b32f5e247637bc) // permutation_comms[61].y
                mstore(0x45a0, 0x0b18c82b44b30ac719309a5bc429fb593724722cafe2a3c47a5c308e1cb21c79) // permutation_comms[62].x
                mstore(0x45c0, 0x06cee596ee25f485be59e36847e4485f2571f2d5f4ed46353a8c2258ae769318) // permutation_comms[62].y
                mstore(0x45e0, 0x23ed734421dc01f2c8cb58226e441018100cedb80a663262bd40279539b001e2) // permutation_comms[63].x
                mstore(0x4600, 0x188f99fdaae207940c69aa77dd68618408a1596ae3eeb77a14b8c47cf4e48ea2) // permutation_comms[63].y
                mstore(0x4620, 0x121a01649ec7b905faa77b3e1a0ae8ffcfb4e432b53ae268143c0b6f56eaca35) // permutation_comms[64].x
                mstore(0x4640, 0x066ec2dc276bee1b98a0f9de397c3ff62f4b0aa3fe757a4d8bd38273d97adddd) // permutation_comms[64].y
                mstore(0x4660, 0x2e73a9f8a75fc6e2802b3166db968b6a2447fbe47d32f83f7541306d9caf120f) // permutation_comms[65].x
                mstore(0x4680, 0x00b6f79fbe9dee0c69ed9ce50e199fe9cbfb37830112df813a8f617498358ac1) // permutation_comms[65].y
                mstore(0x46a0, 0x2a4374a33d625e7f18d8297fc5365c8dc01590b908b98bf035656b680e9976bd) // permutation_comms[66].x
                mstore(0x46c0, 0x1036f1ae28cf1e3ddd8c4e847ae1fccfdf9d84317c6d2c1478f56e58938e960f) // permutation_comms[66].y
                mstore(0x46e0, 0x24324d8ceb0a425a166fffe92508ef92f5d858e55b3effbee5f4a376f57d600d) // permutation_comms[67].x
                mstore(0x4700, 0x28520129c91ddc3a3774ad9a07a88b27a2db5a81a182c691682334ba3738acb7) // permutation_comms[67].y
                mstore(0x4720, 0x1a30b03893ce33de00e2e13a9374700b7096d5e396617124e4768ee240b703e6) // permutation_comms[68].x
                mstore(0x4740, 0x15a3d5e2608a7454de7c3546579e082def969abf7249ea75f55499c9ecc87af6) // permutation_comms[68].y
                mstore(0x4760, 0x2f42adf7e9d3797c9c03b4b5698e418b8d24b158d0b572c3dd3467e070e6b735) // permutation_comms[69].x
                mstore(0x4780, 0x2dc6cb17571f814e9aa7c7affaf080fd4e52e33547919dc21af77bc3625512dd) // permutation_comms[69].y
                mstore(0x47a0, 0x1198deeb89b52db8efe507bad423a92309bf97824633d45546627de5025fad82) // permutation_comms[70].x
                mstore(0x47c0, 0x0f10c54aade6951208be1ba462161cfab93c1ebd46f19027f86f9fd8e67433a4) // permutation_comms[70].y
                mstore(0x47e0, 0x09f8eaa2fc1b279c65768d00d8f0e3a460e1d50a67977d73b59904dd2925e150) // permutation_comms[71].x
                mstore(0x4800, 0x0f45e0c315cc5773aab1f91448523e3da89392b9cf013ec0471553cdf08fcb04) // permutation_comms[71].y
                mstore(0x4820, 0x1c3c57c0748bb71fd34484ea07d5b451a618f1586dabeaeb117095986437f3fa) // permutation_comms[72].x
                mstore(0x4840, 0x255660e9d5d6bda0bdfe920c313f768d5897881735bdf2a7da9d048dbcde396f) // permutation_comms[72].y
                mstore(0x4860, 0x06bf79231c56ee24ee68a77d3e0dbcf5c3bdd352c9865d34d8b201017ee70fcf) // permutation_comms[73].x
                mstore(0x4880, 0x2e16d9fd84865d9fc75d9eb99e7426e1c3b6cce40fdfa2c7aff6428ca8d3e9aa) // permutation_comms[73].y
                mstore(0x48a0, 0x2d92e839e2b620272f3b35e2bb3703cdc1b1a0fc135d04db6f400bc89669f921) // permutation_comms[74].x
                mstore(0x48c0, 0x0200683eda6cffb3ae79bf2ba4506e2d12db8756412398a4e1dd02dde3c8f586) // permutation_comms[74].y
                mstore(0x48e0, 0x22f54ca45c0ce4a2cfecb43904ba43a37155a6f957b8aca50dda7aa3ed17f14e) // permutation_comms[75].x
                mstore(0x4900, 0x1e390a2fe2e5cf6c58cc64615e0febc4aaaeeeac9b96ea1bd8f1c9c406c95020) // permutation_comms[75].y
                mstore(0x4920, 0x2cb49bda04dbe9340276a50686fbb6cd41e71daa3b0309547fdb684cfb24cd84) // permutation_comms[76].x
                mstore(0x4940, 0x1aa4b3077d9e5aafa559142ef0cc1b352368dd96acfa619cadc4f1ab03cc744d) // permutation_comms[76].y
                mstore(0x4960, 0x1f142f817014beb1246def8897eee6049687e9ccfa166e2b77e488853d3a56dd) // permutation_comms[77].x
                mstore(0x4980, 0x23157efaa3b7b3e324133b02c6305ed3b94bd3b72adb000518f8f5a65a02f816) // permutation_comms[77].y
                mstore(0x49a0, 0x17fbdae192128fffa362c3513aa1b444d489b1ca18712edc13da2778aa8901b2) // permutation_comms[78].x
                mstore(0x49c0, 0x230632ab463efe9074669d71e3e27efcf33f547ff4335cd64666cbf97161ada7) // permutation_comms[78].y
                mstore(0x49e0, 0x1659198cc9c0d1201dad7a85ad491eafeecfa5ee4b0896f4c5b47d05659e4560) // permutation_comms[79].x
                mstore(0x4a00, 0x2215c05339007c3bf0313486aab35543fad6b5616a5a4b4a81e7ac5f0a379ac3) // permutation_comms[79].y
                mstore(0x4a20, 0x24d309af0ae33fd0a3c2c86d6d9ad1a6795fc0d1ac41aae1263282a757861617) // permutation_comms[80].x
                mstore(0x4a40, 0x1f0c37d1be8b08e5b03b063395d7a6f167015d9a6aeea0ae1bc503e1c8886d60) // permutation_comms[80].y
                mstore(0x4a60, 0x08566a76ddf63f55e259229ca74dafe4d5dc546ea29a2a2d57d84dea11420bb3) // permutation_comms[81].x
                mstore(0x4a80, 0x30058a3e4b5323914e3243d6e7adeefb34662604d12f517019391fa3e124977c) // permutation_comms[81].y
                mstore(0x4aa0, 0x07db34007cd5087256b5a297f3203c08eb3a46f8e007d89edf5172dd6f38636c) // permutation_comms[82].x
                mstore(0x4ac0, 0x09005f10ec2944d024b5ad507675e6fd45941611efbbca78d2b33192e798d477) // permutation_comms[82].y

                // Read accumulator from instances
                if mload(HAS_ACCUMULATOR_MPTR) {
                    let num_limbs := mload(NUM_ACC_LIMBS_MPTR)
                    let num_limb_bits := mload(NUM_ACC_LIMB_BITS_MPTR)

                    let cptr := add(instances.offset, mul(mload(ACC_OFFSET_MPTR), 0x20))
                    let lhs_y_off := mul(num_limbs, 0x20)
                    let rhs_x_off := mul(lhs_y_off, 2)
                    let rhs_y_off := mul(lhs_y_off, 3)
                    let lhs_x := calldataload(cptr)
                    let lhs_y := calldataload(add(cptr, lhs_y_off))
                    let rhs_x := calldataload(add(cptr, rhs_x_off))
                    let rhs_y := calldataload(add(cptr, rhs_y_off))
                    for
                        {
                            let cptr_end := add(cptr, mul(0x20, num_limbs))
                            let shift := num_limb_bits
                        }
                        lt(cptr, cptr_end)
                        {}
                    {
                        cptr := add(cptr, 0x20)
                        lhs_x := add(lhs_x, shl(shift, calldataload(cptr)))
                        lhs_y := add(lhs_y, shl(shift, calldataload(add(cptr, lhs_y_off))))
                        rhs_x := add(rhs_x, shl(shift, calldataload(add(cptr, rhs_x_off))))
                        rhs_y := add(rhs_y, shl(shift, calldataload(add(cptr, rhs_y_off))))
                        shift := add(shift, num_limb_bits)
                    }

                    success := and(success, eq(mulmod(lhs_y, lhs_y, q), addmod(mulmod(lhs_x, mulmod(lhs_x, lhs_x, q), q), 3, q)))
                    success := and(success, eq(mulmod(rhs_y, rhs_y, q), addmod(mulmod(rhs_x, mulmod(rhs_x, rhs_x, q), q), 3, q)))

                    mstore(ACC_LHS_X_MPTR, lhs_x)
                    mstore(ACC_LHS_Y_MPTR, lhs_y)
                    mstore(ACC_RHS_X_MPTR, rhs_x)
                    mstore(ACC_RHS_Y_MPTR, rhs_y)
                }

                pop(q)
            }

            // Revert earlier if anything from calldata is invalid
            if iszero(success) {
                revert(0, 0)
            }

            // Compute lagrange evaluations and instance evaluation
            {
                let k := mload(K_MPTR)
                let x := mload(X_MPTR)
                let x_n := x
                for
                    { let idx := 0 }
                    lt(idx, k)
                    { idx := add(idx, 1) }
                {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(OMEGA_MPTR)

                let mptr := X_N_MPTR
                let mptr_end := add(mptr, mul(0x20, add(mload(NUM_INSTANCES_MPTR), 6)))
                if iszero(mload(NUM_INSTANCES_MPTR)) {
                    mptr_end := add(mptr_end, 0x20)
                }
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, X_N_MPTR, add(mptr_end, 0x20))

                mptr := X_N_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                let l_blind := mload(add(X_N_MPTR, 0x20))
                let l_i_cptr := add(X_N_MPTR, 0x40)
                for
                    { let l_i_cptr_end := add(X_N_MPTR, 0xc0) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) }
                {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                let instance_eval := 0
                for
                    {
                        let instance_cptr := instances.offset
                        let instance_cptr_end := add(instance_cptr, mul(0x20, mload(NUM_INSTANCES_MPTR)))
                    }
                    lt(instance_cptr, instance_cptr_end)
                    {
                        instance_cptr := add(instance_cptr, 0x20)
                        l_i_cptr := add(l_i_cptr, 0x20)
                    }
                {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(X_N_MPTR)
                let l_0 := mload(add(X_N_MPTR, 0xc0))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            // Compute quotient evavluation
            {
                let quotient_eval_numer
                let y := mload(Y_MPTR)
                {
                    let f_82 := calldataload(0x5864)
                    let var0 := 0x2
                    let var1 := sub(R, f_82)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_82, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_52 := calldataload(0x48e4)
                    let a_0 := calldataload(0x4264)
                    let a_26 := calldataload(0x45a4)
                    let var10 := addmod(a_0, a_26, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_52, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := var13
                }
                {
                    let f_82 := calldataload(0x5864)
                    let var0 := 0x1
                    let var1 := sub(R, f_82)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_82, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_53 := calldataload(0x4904)
                    let a_1 := calldataload(0x4284)
                    let a_27 := calldataload(0x45c4)
                    let var10 := addmod(a_1, a_27, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_53, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_83 := calldataload(0x5884)
                    let var0 := 0x1
                    let var1 := sub(R, f_83)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_83, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_54 := calldataload(0x4924)
                    let a_2 := calldataload(0x42a4)
                    let a_28 := calldataload(0x45e4)
                    let var10 := addmod(a_2, a_28, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_54, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_84 := calldataload(0x58a4)
                    let var0 := 0x1
                    let var1 := sub(R, f_84)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_84, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_55 := calldataload(0x4944)
                    let a_3 := calldataload(0x42c4)
                    let a_29 := calldataload(0x4604)
                    let var10 := addmod(a_3, a_29, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_55, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_84 := calldataload(0x58a4)
                    let var0 := 0x1
                    let var1 := sub(R, f_84)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_84, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_56 := calldataload(0x4964)
                    let a_4 := calldataload(0x42e4)
                    let a_30 := calldataload(0x4624)
                    let var10 := addmod(a_4, a_30, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_56, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_85 := calldataload(0x58c4)
                    let var0 := 0x1
                    let var1 := sub(R, f_85)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_85, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_57 := calldataload(0x4984)
                    let a_5 := calldataload(0x4304)
                    let a_31 := calldataload(0x4644)
                    let var10 := addmod(a_5, a_31, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_57, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_85 := calldataload(0x58c4)
                    let var0 := 0x1
                    let var1 := sub(R, f_85)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_85, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_58 := calldataload(0x49a4)
                    let a_6 := calldataload(0x4324)
                    let a_32 := calldataload(0x4664)
                    let var10 := addmod(a_6, a_32, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_58, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_85 := calldataload(0x58c4)
                    let var0 := 0x1
                    let var1 := sub(R, f_85)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_85, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_59 := calldataload(0x49c4)
                    let a_7 := calldataload(0x4344)
                    let a_33 := calldataload(0x4684)
                    let var10 := addmod(a_7, a_33, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_59, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_90 := calldataload(0x5964)
                    let var0 := 0x2
                    let var1 := sub(R, f_90)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_90, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_60 := calldataload(0x49e4)
                    let a_8 := calldataload(0x4364)
                    let a_34 := calldataload(0x46a4)
                    let var10 := addmod(a_8, a_34, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_60, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_91 := calldataload(0x5984)
                    let var0 := 0x2
                    let var1 := sub(R, f_91)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_91, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_61 := calldataload(0x4a04)
                    let a_9 := calldataload(0x4384)
                    let a_35 := calldataload(0x46c4)
                    let var10 := addmod(a_9, a_35, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_61, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_92 := calldataload(0x59a4)
                    let var0 := 0x2
                    let var1 := sub(R, f_92)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_92, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_62 := calldataload(0x4a24)
                    let a_10 := calldataload(0x43a4)
                    let a_36 := calldataload(0x46e4)
                    let var10 := addmod(a_10, a_36, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_62, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_93 := calldataload(0x59c4)
                    let var0 := 0x2
                    let var1 := sub(R, f_93)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_93, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_63 := calldataload(0x4a44)
                    let a_11 := calldataload(0x43c4)
                    let a_37 := calldataload(0x4704)
                    let var10 := addmod(a_11, a_37, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_63, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_94 := calldataload(0x59e4)
                    let var0 := 0x2
                    let var1 := sub(R, f_94)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_94, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let var10 := 0x5
                    let var11 := addmod(var10, var1, R)
                    let var12 := mulmod(var9, var11, R)
                    let a_64 := calldataload(0x4a64)
                    let a_12 := calldataload(0x43e4)
                    let a_38 := calldataload(0x4724)
                    let var13 := addmod(a_12, a_38, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_64, var14, R)
                    let var16 := mulmod(var12, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_87 := calldataload(0x5904)
                    let var0 := 0x1
                    let var1 := sub(R, f_87)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_87, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_65 := calldataload(0x4a84)
                    let a_13 := calldataload(0x4404)
                    let a_39 := calldataload(0x4744)
                    let var10 := addmod(a_13, a_39, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_65, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_94 := calldataload(0x59e4)
                    let var0 := 0x1
                    let var1 := sub(R, f_94)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_94, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let var10 := 0x5
                    let var11 := addmod(var10, var1, R)
                    let var12 := mulmod(var9, var11, R)
                    let a_66 := calldataload(0x4aa4)
                    let a_14 := calldataload(0x4424)
                    let a_40 := calldataload(0x4764)
                    let var13 := addmod(a_14, a_40, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_66, var14, R)
                    let var16 := mulmod(var12, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_89 := calldataload(0x5944)
                    let var0 := 0x1
                    let var1 := sub(R, f_89)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_89, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_67 := calldataload(0x4ac4)
                    let a_15 := calldataload(0x4444)
                    let a_41 := calldataload(0x4784)
                    let var10 := addmod(a_15, a_41, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_67, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_94 := calldataload(0x59e4)
                    let var0 := 0x1
                    let var1 := sub(R, f_94)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_94, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let var10 := 0x5
                    let var11 := addmod(var10, var1, R)
                    let var12 := mulmod(var9, var11, R)
                    let a_68 := calldataload(0x4ae4)
                    let a_16 := calldataload(0x4464)
                    let a_42 := calldataload(0x47a4)
                    let var13 := addmod(a_16, a_42, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_68, var14, R)
                    let var16 := mulmod(var12, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_94 := calldataload(0x59e4)
                    let var0 := 0x1
                    let var1 := sub(R, f_94)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_94, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let var10 := 0x5
                    let var11 := addmod(var10, var1, R)
                    let var12 := mulmod(var9, var11, R)
                    let a_69 := calldataload(0x4b04)
                    let a_17 := calldataload(0x4484)
                    let a_43 := calldataload(0x47c4)
                    let var13 := addmod(a_17, a_43, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_69, var14, R)
                    let var16 := mulmod(var12, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_95 := calldataload(0x5a04)
                    let var0 := 0x1
                    let var1 := sub(R, f_95)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_95, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_70 := calldataload(0x4b24)
                    let a_18 := calldataload(0x44a4)
                    let a_44 := calldataload(0x47e4)
                    let var10 := addmod(a_18, a_44, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_70, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_96 := calldataload(0x5a24)
                    let var0 := 0x2
                    let var1 := sub(R, f_96)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_96, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_71 := calldataload(0x4b44)
                    let a_19 := calldataload(0x44c4)
                    let a_45 := calldataload(0x4804)
                    let var10 := addmod(a_19, a_45, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_71, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_97 := calldataload(0x5a44)
                    let var0 := 0x2
                    let var1 := sub(R, f_97)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_97, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_72 := calldataload(0x4b64)
                    let a_20 := calldataload(0x44e4)
                    let a_46 := calldataload(0x4824)
                    let var10 := addmod(a_20, a_46, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_72, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_98 := calldataload(0x5a64)
                    let var0 := 0x2
                    let var1 := sub(R, f_98)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_98, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_73 := calldataload(0x4b84)
                    let a_21 := calldataload(0x4504)
                    let a_47 := calldataload(0x4844)
                    let var10 := addmod(a_21, a_47, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_73, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_99 := calldataload(0x5a84)
                    let var0 := 0x2
                    let var1 := sub(R, f_99)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_99, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_74 := calldataload(0x4ba4)
                    let a_22 := calldataload(0x4524)
                    let a_48 := calldataload(0x4864)
                    let var10 := addmod(a_22, a_48, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_74, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_100 := calldataload(0x5aa4)
                    let var0 := 0x2
                    let var1 := sub(R, f_100)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_100, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_75 := calldataload(0x4bc4)
                    let a_23 := calldataload(0x4544)
                    let a_49 := calldataload(0x4884)
                    let var10 := addmod(a_23, a_49, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_75, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_101 := calldataload(0x5ac4)
                    let var0 := 0x2
                    let var1 := sub(R, f_101)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_101, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_76 := calldataload(0x4be4)
                    let a_24 := calldataload(0x4564)
                    let a_50 := calldataload(0x48a4)
                    let var10 := addmod(a_24, a_50, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_76, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_102 := calldataload(0x5ae4)
                    let var0 := 0x2
                    let var1 := sub(R, f_102)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_102, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_77 := calldataload(0x4c04)
                    let a_25 := calldataload(0x4584)
                    let a_51 := calldataload(0x48c4)
                    let var10 := addmod(a_25, a_51, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_77, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_82 := calldataload(0x5864)
                    let var0 := 0x1
                    let var1 := sub(R, f_82)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_82, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_52 := calldataload(0x48e4)
                    let a_0 := calldataload(0x4264)
                    let a_26 := calldataload(0x45a4)
                    let var10 := mulmod(a_0, a_26, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_52, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_83 := calldataload(0x5884)
                    let var0 := 0x1
                    let var1 := sub(R, f_83)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_83, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_53 := calldataload(0x4904)
                    let a_1 := calldataload(0x4284)
                    let a_27 := calldataload(0x45c4)
                    let var10 := mulmod(a_1, a_27, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_53, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_84 := calldataload(0x58a4)
                    let var0 := 0x2
                    let var1 := sub(R, f_84)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_84, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_54 := calldataload(0x4924)
                    let a_2 := calldataload(0x42a4)
                    let a_28 := calldataload(0x45e4)
                    let var10 := mulmod(a_2, a_28, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_54, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_85 := calldataload(0x58c4)
                    let var0 := 0x2
                    let var1 := sub(R, f_85)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_85, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_55 := calldataload(0x4944)
                    let a_3 := calldataload(0x42c4)
                    let a_29 := calldataload(0x4604)
                    let var10 := mulmod(a_3, a_29, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_55, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_86 := calldataload(0x58e4)
                    let var0 := 0x1
                    let var1 := sub(R, f_86)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_86, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_56 := calldataload(0x4964)
                    let a_4 := calldataload(0x42e4)
                    let a_30 := calldataload(0x4624)
                    let var10 := mulmod(a_4, a_30, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_56, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_87 := calldataload(0x5904)
                    let var0 := 0x1
                    let var1 := sub(R, f_87)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_87, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_57 := calldataload(0x4984)
                    let a_5 := calldataload(0x4304)
                    let a_31 := calldataload(0x4644)
                    let var10 := mulmod(a_5, a_31, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_57, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_88 := calldataload(0x5924)
                    let var0 := 0x1
                    let var1 := sub(R, f_88)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_88, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_58 := calldataload(0x49a4)
                    let a_6 := calldataload(0x4324)
                    let a_32 := calldataload(0x4664)
                    let var10 := mulmod(a_6, a_32, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_58, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_89 := calldataload(0x5944)
                    let var0 := 0x1
                    let var1 := sub(R, f_89)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_89, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_59 := calldataload(0x49c4)
                    let a_7 := calldataload(0x4344)
                    let a_33 := calldataload(0x4684)
                    let var10 := mulmod(a_7, a_33, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_59, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_90 := calldataload(0x5964)
                    let var0 := 0x1
                    let var1 := sub(R, f_90)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_90, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_60 := calldataload(0x49e4)
                    let a_8 := calldataload(0x4364)
                    let a_34 := calldataload(0x46a4)
                    let var10 := mulmod(a_8, a_34, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_60, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_91 := calldataload(0x5984)
                    let var0 := 0x1
                    let var1 := sub(R, f_91)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_91, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_61 := calldataload(0x4a04)
                    let a_9 := calldataload(0x4384)
                    let a_35 := calldataload(0x46c4)
                    let var10 := mulmod(a_9, a_35, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_61, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_92 := calldataload(0x59a4)
                    let var0 := 0x1
                    let var1 := sub(R, f_92)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_92, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_62 := calldataload(0x4a24)
                    let a_10 := calldataload(0x43a4)
                    let a_36 := calldataload(0x46e4)
                    let var10 := mulmod(a_10, a_36, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_62, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_93 := calldataload(0x59c4)
                    let var0 := 0x1
                    let var1 := sub(R, f_93)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_93, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_63 := calldataload(0x4a44)
                    let a_11 := calldataload(0x43c4)
                    let a_37 := calldataload(0x4704)
                    let var10 := mulmod(a_11, a_37, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_63, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_86 := calldataload(0x58e4)
                    let var0 := 0x1
                    let var1 := sub(R, f_86)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_86, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_64 := calldataload(0x4a64)
                    let a_12 := calldataload(0x43e4)
                    let a_38 := calldataload(0x4724)
                    let var10 := mulmod(a_12, a_38, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_64, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_88 := calldataload(0x5924)
                    let var0 := 0x1
                    let var1 := sub(R, f_88)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_88, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_65 := calldataload(0x4a84)
                    let a_13 := calldataload(0x4404)
                    let a_39 := calldataload(0x4744)
                    let var10 := mulmod(a_13, a_39, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_65, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_89 := calldataload(0x5944)
                    let var0 := 0x1
                    let var1 := sub(R, f_89)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_89, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_66 := calldataload(0x4aa4)
                    let a_14 := calldataload(0x4424)
                    let a_40 := calldataload(0x4764)
                    let var10 := mulmod(a_14, a_40, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_66, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_91 := calldataload(0x5984)
                    let var0 := 0x1
                    let var1 := sub(R, f_91)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_91, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_67 := calldataload(0x4ac4)
                    let a_15 := calldataload(0x4444)
                    let a_41 := calldataload(0x4784)
                    let var10 := mulmod(a_15, a_41, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_67, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_93 := calldataload(0x59c4)
                    let var0 := 0x1
                    let var1 := sub(R, f_93)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_93, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_68 := calldataload(0x4ae4)
                    let a_16 := calldataload(0x4464)
                    let a_42 := calldataload(0x47a4)
                    let var10 := mulmod(a_16, a_42, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_68, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_95 := calldataload(0x5a04)
                    let var0 := 0x2
                    let var1 := sub(R, f_95)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_95, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_69 := calldataload(0x4b04)
                    let a_17 := calldataload(0x4484)
                    let a_43 := calldataload(0x47c4)
                    let var10 := mulmod(a_17, a_43, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_69, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_95 := calldataload(0x5a04)
                    let var0 := 0x1
                    let var1 := sub(R, f_95)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_95, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_70 := calldataload(0x4b24)
                    let a_18 := calldataload(0x44a4)
                    let a_44 := calldataload(0x47e4)
                    let var10 := mulmod(a_18, a_44, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_70, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_96 := calldataload(0x5a24)
                    let var0 := 0x1
                    let var1 := sub(R, f_96)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_96, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_71 := calldataload(0x4b44)
                    let a_19 := calldataload(0x44c4)
                    let a_45 := calldataload(0x4804)
                    let var10 := mulmod(a_19, a_45, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_71, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_97 := calldataload(0x5a44)
                    let var0 := 0x1
                    let var1 := sub(R, f_97)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_97, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_72 := calldataload(0x4b64)
                    let a_20 := calldataload(0x44e4)
                    let a_46 := calldataload(0x4824)
                    let var10 := mulmod(a_20, a_46, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_72, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_98 := calldataload(0x5a64)
                    let var0 := 0x1
                    let var1 := sub(R, f_98)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_98, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_73 := calldataload(0x4b84)
                    let a_21 := calldataload(0x4504)
                    let a_47 := calldataload(0x4844)
                    let var10 := mulmod(a_21, a_47, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_73, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_99 := calldataload(0x5a84)
                    let var0 := 0x1
                    let var1 := sub(R, f_99)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_99, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_74 := calldataload(0x4ba4)
                    let a_22 := calldataload(0x4524)
                    let a_48 := calldataload(0x4864)
                    let var10 := mulmod(a_22, a_48, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_74, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_100 := calldataload(0x5aa4)
                    let var0 := 0x1
                    let var1 := sub(R, f_100)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_100, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_75 := calldataload(0x4bc4)
                    let a_23 := calldataload(0x4544)
                    let a_49 := calldataload(0x4884)
                    let var10 := mulmod(a_23, a_49, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_75, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_101 := calldataload(0x5ac4)
                    let var0 := 0x1
                    let var1 := sub(R, f_101)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_101, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_76 := calldataload(0x4be4)
                    let a_24 := calldataload(0x4564)
                    let a_50 := calldataload(0x48a4)
                    let var10 := mulmod(a_24, a_50, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_76, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_102 := calldataload(0x5ae4)
                    let var0 := 0x1
                    let var1 := sub(R, f_102)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_102, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_77 := calldataload(0x4c04)
                    let a_25 := calldataload(0x4584)
                    let a_51 := calldataload(0x48c4)
                    let var10 := mulmod(a_25, a_51, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_77, var11, R)
                    let var13 := mulmod(var9, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_82 := calldataload(0x5864)
                    let var0 := 0x1
                    let var1 := sub(R, f_82)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_82, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_52 := calldataload(0x48e4)
                    let a_0 := calldataload(0x4264)
                    let a_26 := calldataload(0x45a4)
                    let var10 := sub(R, a_26)
                    let var11 := addmod(a_0, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_52, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_83 := calldataload(0x5884)
                    let var0 := 0x2
                    let var1 := sub(R, f_83)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_83, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_53 := calldataload(0x4904)
                    let a_1 := calldataload(0x4284)
                    let a_27 := calldataload(0x45c4)
                    let var10 := sub(R, a_27)
                    let var11 := addmod(a_1, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_53, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_83 := calldataload(0x5884)
                    let var0 := 0x1
                    let var1 := sub(R, f_83)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_83, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_54 := calldataload(0x4924)
                    let a_2 := calldataload(0x42a4)
                    let a_28 := calldataload(0x45e4)
                    let var10 := sub(R, a_28)
                    let var11 := addmod(a_2, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_54, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_84 := calldataload(0x58a4)
                    let var0 := 0x1
                    let var1 := sub(R, f_84)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_84, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_55 := calldataload(0x4944)
                    let a_3 := calldataload(0x42c4)
                    let a_29 := calldataload(0x4604)
                    let var10 := sub(R, a_29)
                    let var11 := addmod(a_3, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_55, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_86 := calldataload(0x58e4)
                    let var0 := 0x2
                    let var1 := sub(R, f_86)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_86, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_56 := calldataload(0x4964)
                    let a_4 := calldataload(0x42e4)
                    let a_30 := calldataload(0x4624)
                    let var10 := sub(R, a_30)
                    let var11 := addmod(a_4, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_56, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_87 := calldataload(0x5904)
                    let var0 := 0x2
                    let var1 := sub(R, f_87)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_87, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_57 := calldataload(0x4984)
                    let a_5 := calldataload(0x4304)
                    let a_31 := calldataload(0x4644)
                    let var10 := sub(R, a_31)
                    let var11 := addmod(a_5, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_57, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_88 := calldataload(0x5924)
                    let var0 := 0x2
                    let var1 := sub(R, f_88)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_88, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_58 := calldataload(0x49a4)
                    let a_6 := calldataload(0x4324)
                    let a_32 := calldataload(0x4664)
                    let var10 := sub(R, a_32)
                    let var11 := addmod(a_6, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_58, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_89 := calldataload(0x5944)
                    let var0 := 0x2
                    let var1 := sub(R, f_89)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_89, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_59 := calldataload(0x49c4)
                    let a_7 := calldataload(0x4344)
                    let a_33 := calldataload(0x4684)
                    let var10 := sub(R, a_33)
                    let var11 := addmod(a_7, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_59, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_90 := calldataload(0x5964)
                    let var0 := 0x1
                    let var1 := sub(R, f_90)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_90, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_60 := calldataload(0x49e4)
                    let a_8 := calldataload(0x4364)
                    let a_34 := calldataload(0x46a4)
                    let var10 := sub(R, a_34)
                    let var11 := addmod(a_8, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_60, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_91 := calldataload(0x5984)
                    let var0 := 0x1
                    let var1 := sub(R, f_91)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_91, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_61 := calldataload(0x4a04)
                    let a_9 := calldataload(0x4384)
                    let a_35 := calldataload(0x46c4)
                    let var10 := sub(R, a_35)
                    let var11 := addmod(a_9, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_61, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_92 := calldataload(0x59a4)
                    let var0 := 0x1
                    let var1 := sub(R, f_92)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_92, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_62 := calldataload(0x4a24)
                    let a_10 := calldataload(0x43a4)
                    let a_36 := calldataload(0x46e4)
                    let var10 := sub(R, a_36)
                    let var11 := addmod(a_10, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_62, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_93 := calldataload(0x59c4)
                    let var0 := 0x1
                    let var1 := sub(R, f_93)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_93, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_63 := calldataload(0x4a44)
                    let a_11 := calldataload(0x43c4)
                    let a_37 := calldataload(0x4704)
                    let var10 := sub(R, a_37)
                    let var11 := addmod(a_11, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_63, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_86 := calldataload(0x58e4)
                    let var0 := 0x1
                    let var1 := sub(R, f_86)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_86, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_64 := calldataload(0x4a64)
                    let a_12 := calldataload(0x43e4)
                    let a_38 := calldataload(0x4724)
                    let var10 := sub(R, a_38)
                    let var11 := addmod(a_12, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_64, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_87 := calldataload(0x5904)
                    let var0 := 0x1
                    let var1 := sub(R, f_87)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_87, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_65 := calldataload(0x4a84)
                    let a_13 := calldataload(0x4404)
                    let a_39 := calldataload(0x4744)
                    let var10 := sub(R, a_39)
                    let var11 := addmod(a_13, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_65, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_88 := calldataload(0x5924)
                    let var0 := 0x1
                    let var1 := sub(R, f_88)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_88, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_66 := calldataload(0x4aa4)
                    let a_14 := calldataload(0x4424)
                    let a_40 := calldataload(0x4764)
                    let var10 := sub(R, a_40)
                    let var11 := addmod(a_14, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_66, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_90 := calldataload(0x5964)
                    let var0 := 0x1
                    let var1 := sub(R, f_90)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_90, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_67 := calldataload(0x4ac4)
                    let a_15 := calldataload(0x4444)
                    let a_41 := calldataload(0x4784)
                    let var10 := sub(R, a_41)
                    let var11 := addmod(a_15, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_67, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_92 := calldataload(0x59a4)
                    let var0 := 0x1
                    let var1 := sub(R, f_92)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_92, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_68 := calldataload(0x4ae4)
                    let a_16 := calldataload(0x4464)
                    let a_42 := calldataload(0x47a4)
                    let var10 := sub(R, a_42)
                    let var11 := addmod(a_16, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_68, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_94 := calldataload(0x59e4)
                    let var0 := 0x1
                    let var1 := sub(R, f_94)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_94, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let var10 := 0x4
                    let var11 := addmod(var10, var1, R)
                    let var12 := mulmod(var9, var11, R)
                    let a_69 := calldataload(0x4b04)
                    let a_17 := calldataload(0x4484)
                    let a_43 := calldataload(0x47c4)
                    let var13 := sub(R, a_43)
                    let var14 := addmod(a_17, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_69, var15, R)
                    let var17 := mulmod(var12, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_95 := calldataload(0x5a04)
                    let var0 := 0x1
                    let var1 := sub(R, f_95)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_95, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_70 := calldataload(0x4b24)
                    let a_18 := calldataload(0x44a4)
                    let a_44 := calldataload(0x47e4)
                    let var10 := sub(R, a_44)
                    let var11 := addmod(a_18, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_70, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_96 := calldataload(0x5a24)
                    let var0 := 0x1
                    let var1 := sub(R, f_96)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_96, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_71 := calldataload(0x4b44)
                    let a_19 := calldataload(0x44c4)
                    let a_45 := calldataload(0x4804)
                    let var10 := sub(R, a_45)
                    let var11 := addmod(a_19, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_71, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_97 := calldataload(0x5a44)
                    let var0 := 0x1
                    let var1 := sub(R, f_97)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_97, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_72 := calldataload(0x4b64)
                    let a_20 := calldataload(0x44e4)
                    let a_46 := calldataload(0x4824)
                    let var10 := sub(R, a_46)
                    let var11 := addmod(a_20, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_72, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_98 := calldataload(0x5a64)
                    let var0 := 0x1
                    let var1 := sub(R, f_98)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_98, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_73 := calldataload(0x4b84)
                    let a_21 := calldataload(0x4504)
                    let a_47 := calldataload(0x4844)
                    let var10 := sub(R, a_47)
                    let var11 := addmod(a_21, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_73, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_99 := calldataload(0x5a84)
                    let var0 := 0x1
                    let var1 := sub(R, f_99)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_99, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_74 := calldataload(0x4ba4)
                    let a_22 := calldataload(0x4524)
                    let a_48 := calldataload(0x4864)
                    let var10 := sub(R, a_48)
                    let var11 := addmod(a_22, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_74, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_100 := calldataload(0x5aa4)
                    let var0 := 0x1
                    let var1 := sub(R, f_100)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_100, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_75 := calldataload(0x4bc4)
                    let a_23 := calldataload(0x4544)
                    let a_49 := calldataload(0x4884)
                    let var10 := sub(R, a_49)
                    let var11 := addmod(a_23, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_75, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_101 := calldataload(0x5ac4)
                    let var0 := 0x1
                    let var1 := sub(R, f_101)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_101, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_76 := calldataload(0x4be4)
                    let a_24 := calldataload(0x4564)
                    let a_50 := calldataload(0x48a4)
                    let var10 := sub(R, a_50)
                    let var11 := addmod(a_24, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_76, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_102 := calldataload(0x5ae4)
                    let var0 := 0x1
                    let var1 := sub(R, f_102)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_102, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_77 := calldataload(0x4c04)
                    let a_25 := calldataload(0x4584)
                    let a_51 := calldataload(0x48c4)
                    let var10 := sub(R, a_51)
                    let var11 := addmod(a_25, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_77, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_103 := calldataload(0x5b04)
                    let var0 := 0x1
                    let var1 := sub(R, f_103)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_103, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_52 := calldataload(0x48e4)
                    let a_52_prev_1 := calldataload(0x4c84)
                    let var7 := 0x0
                    let a_0 := calldataload(0x4264)
                    let a_26 := calldataload(0x45a4)
                    let var8 := mulmod(a_0, a_26, R)
                    let var9 := addmod(var7, var8, R)
                    let a_1 := calldataload(0x4284)
                    let a_27 := calldataload(0x45c4)
                    let var10 := mulmod(a_1, a_27, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := addmod(a_52_prev_1, var11, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_52, var13, R)
                    let var15 := mulmod(var6, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_99 := calldataload(0x5a84)
                    let var0 := 0x1
                    let var1 := sub(R, f_99)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_99, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_54 := calldataload(0x4924)
                    let a_54_prev_1 := calldataload(0x4ca4)
                    let var10 := 0x0
                    let a_2 := calldataload(0x42a4)
                    let a_28 := calldataload(0x45e4)
                    let var11 := mulmod(a_2, a_28, R)
                    let var12 := addmod(var10, var11, R)
                    let a_3 := calldataload(0x42c4)
                    let a_29 := calldataload(0x4604)
                    let var13 := mulmod(a_3, a_29, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := addmod(a_54_prev_1, var14, R)
                    let var16 := sub(R, var15)
                    let var17 := addmod(a_54, var16, R)
                    let var18 := mulmod(var9, var17, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var18, r)
                }
                {
                    let f_105 := calldataload(0x5b44)
                    let var0 := 0x2
                    let var1 := sub(R, f_105)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_105, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_56 := calldataload(0x4964)
                    let a_56_prev_1 := calldataload(0x4cc4)
                    let var7 := 0x0
                    let a_4 := calldataload(0x42e4)
                    let a_30 := calldataload(0x4624)
                    let var8 := mulmod(a_4, a_30, R)
                    let var9 := addmod(var7, var8, R)
                    let a_5 := calldataload(0x4304)
                    let a_31 := calldataload(0x4644)
                    let var10 := mulmod(a_5, a_31, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := addmod(a_56_prev_1, var11, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_56, var13, R)
                    let var15 := mulmod(var6, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_106 := calldataload(0x5b64)
                    let var0 := 0x1
                    let var1 := sub(R, f_106)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_106, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_58 := calldataload(0x49a4)
                    let a_58_prev_1 := calldataload(0x4ce4)
                    let var10 := 0x0
                    let a_6 := calldataload(0x4324)
                    let a_32 := calldataload(0x4664)
                    let var11 := mulmod(a_6, a_32, R)
                    let var12 := addmod(var10, var11, R)
                    let a_7 := calldataload(0x4344)
                    let a_33 := calldataload(0x4684)
                    let var13 := mulmod(a_7, a_33, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := addmod(a_58_prev_1, var14, R)
                    let var16 := sub(R, var15)
                    let var17 := addmod(a_58, var16, R)
                    let var18 := mulmod(var9, var17, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var18, r)
                }
                {
                    let f_108 := calldataload(0x5ba4)
                    let var0 := 0x1
                    let var1 := sub(R, f_108)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_108, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_60 := calldataload(0x49e4)
                    let a_60_prev_1 := calldataload(0x4d04)
                    let var10 := 0x0
                    let a_8 := calldataload(0x4364)
                    let a_34 := calldataload(0x46a4)
                    let var11 := mulmod(a_8, a_34, R)
                    let var12 := addmod(var10, var11, R)
                    let a_9 := calldataload(0x4384)
                    let a_35 := calldataload(0x46c4)
                    let var13 := mulmod(a_9, a_35, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := addmod(a_60_prev_1, var14, R)
                    let var16 := sub(R, var15)
                    let var17 := addmod(a_60, var16, R)
                    let var18 := mulmod(var9, var17, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var18, r)
                }
                {
                    let f_110 := calldataload(0x5be4)
                    let var0 := 0x1
                    let var1 := sub(R, f_110)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_110, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_62 := calldataload(0x4a24)
                    let a_62_prev_1 := calldataload(0x4d24)
                    let var7 := 0x0
                    let a_10 := calldataload(0x43a4)
                    let a_36 := calldataload(0x46e4)
                    let var8 := mulmod(a_10, a_36, R)
                    let var9 := addmod(var7, var8, R)
                    let a_11 := calldataload(0x43c4)
                    let a_37 := calldataload(0x4704)
                    let var10 := mulmod(a_11, a_37, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := addmod(a_62_prev_1, var11, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_62, var13, R)
                    let var15 := mulmod(var6, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_112 := calldataload(0x5c24)
                    let var0 := 0x2
                    let var1 := sub(R, f_112)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_112, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_64 := calldataload(0x4a64)
                    let a_64_prev_1 := calldataload(0x4d44)
                    let var7 := 0x0
                    let a_12 := calldataload(0x43e4)
                    let a_38 := calldataload(0x4724)
                    let var8 := mulmod(a_12, a_38, R)
                    let var9 := addmod(var7, var8, R)
                    let a_13 := calldataload(0x4404)
                    let a_39 := calldataload(0x4744)
                    let var10 := mulmod(a_13, a_39, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := addmod(a_64_prev_1, var11, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_64, var13, R)
                    let var15 := mulmod(var6, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_113 := calldataload(0x5c44)
                    let var0 := 0x1
                    let var1 := sub(R, f_113)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_113, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_66 := calldataload(0x4aa4)
                    let a_66_prev_1 := calldataload(0x4d64)
                    let var10 := 0x0
                    let a_14 := calldataload(0x4424)
                    let a_40 := calldataload(0x4764)
                    let var11 := mulmod(a_14, a_40, R)
                    let var12 := addmod(var10, var11, R)
                    let a_15 := calldataload(0x4444)
                    let a_41 := calldataload(0x4784)
                    let var13 := mulmod(a_15, a_41, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := addmod(a_66_prev_1, var14, R)
                    let var16 := sub(R, var15)
                    let var17 := addmod(a_66, var16, R)
                    let var18 := mulmod(var9, var17, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var18, r)
                }
                {
                    let f_115 := calldataload(0x5c84)
                    let var0 := 0x1
                    let var1 := sub(R, f_115)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_115, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_68 := calldataload(0x4ae4)
                    let a_68_prev_1 := calldataload(0x4d84)
                    let var10 := 0x0
                    let a_16 := calldataload(0x4464)
                    let a_42 := calldataload(0x47a4)
                    let var11 := mulmod(a_16, a_42, R)
                    let var12 := addmod(var10, var11, R)
                    let a_17 := calldataload(0x4484)
                    let a_43 := calldataload(0x47c4)
                    let var13 := mulmod(a_17, a_43, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := addmod(a_68_prev_1, var14, R)
                    let var16 := sub(R, var15)
                    let var17 := addmod(a_68, var16, R)
                    let var18 := mulmod(var9, var17, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var18, r)
                }
                {
                    let f_117 := calldataload(0x5cc4)
                    let var0 := 0x1
                    let var1 := sub(R, f_117)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_117, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_70 := calldataload(0x4b24)
                    let a_70_prev_1 := calldataload(0x4da4)
                    let var7 := 0x0
                    let a_18 := calldataload(0x44a4)
                    let a_44 := calldataload(0x47e4)
                    let var8 := mulmod(a_18, a_44, R)
                    let var9 := addmod(var7, var8, R)
                    let a_19 := calldataload(0x44c4)
                    let a_45 := calldataload(0x4804)
                    let var10 := mulmod(a_19, a_45, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := addmod(a_70_prev_1, var11, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_70, var13, R)
                    let var15 := mulmod(var6, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_119 := calldataload(0x5d04)
                    let var0 := 0x2
                    let var1 := sub(R, f_119)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_119, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_72 := calldataload(0x4b64)
                    let a_72_prev_1 := calldataload(0x4dc4)
                    let var7 := 0x0
                    let a_20 := calldataload(0x44e4)
                    let a_46 := calldataload(0x4824)
                    let var8 := mulmod(a_20, a_46, R)
                    let var9 := addmod(var7, var8, R)
                    let a_21 := calldataload(0x4504)
                    let a_47 := calldataload(0x4844)
                    let var10 := mulmod(a_21, a_47, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := addmod(a_72_prev_1, var11, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_72, var13, R)
                    let var15 := mulmod(var6, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_120 := calldataload(0x5d24)
                    let var0 := 0x1
                    let var1 := sub(R, f_120)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_120, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_74 := calldataload(0x4ba4)
                    let a_74_prev_1 := calldataload(0x4de4)
                    let var10 := 0x0
                    let a_22 := calldataload(0x4524)
                    let a_48 := calldataload(0x4864)
                    let var11 := mulmod(a_22, a_48, R)
                    let var12 := addmod(var10, var11, R)
                    let a_23 := calldataload(0x4544)
                    let a_49 := calldataload(0x4884)
                    let var13 := mulmod(a_23, a_49, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := addmod(a_74_prev_1, var14, R)
                    let var16 := sub(R, var15)
                    let var17 := addmod(a_74, var16, R)
                    let var18 := mulmod(var9, var17, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var18, r)
                }
                {
                    let f_122 := calldataload(0x5d64)
                    let var0 := 0x1
                    let var1 := sub(R, f_122)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_122, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_76 := calldataload(0x4be4)
                    let a_76_prev_1 := calldataload(0x4e04)
                    let var10 := 0x0
                    let a_24 := calldataload(0x4564)
                    let a_50 := calldataload(0x48a4)
                    let var11 := mulmod(a_24, a_50, R)
                    let var12 := addmod(var10, var11, R)
                    let a_25 := calldataload(0x4584)
                    let a_51 := calldataload(0x48c4)
                    let var13 := mulmod(a_25, a_51, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := addmod(a_76_prev_1, var14, R)
                    let var16 := sub(R, var15)
                    let var17 := addmod(a_76, var16, R)
                    let var18 := mulmod(var9, var17, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var18, r)
                }
                {
                    let f_103 := calldataload(0x5b04)
                    let var0 := 0x2
                    let var1 := sub(R, f_103)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_103, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_52 := calldataload(0x48e4)
                    let var7 := 0x0
                    let a_0 := calldataload(0x4264)
                    let a_26 := calldataload(0x45a4)
                    let var8 := mulmod(a_0, a_26, R)
                    let var9 := addmod(var7, var8, R)
                    let a_1 := calldataload(0x4284)
                    let a_27 := calldataload(0x45c4)
                    let var10 := mulmod(a_1, a_27, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_52, var12, R)
                    let var14 := mulmod(var6, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_101 := calldataload(0x5ac4)
                    let var0 := 0x1
                    let var1 := sub(R, f_101)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_101, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_54 := calldataload(0x4924)
                    let var10 := 0x0
                    let a_2 := calldataload(0x42a4)
                    let a_28 := calldataload(0x45e4)
                    let var11 := mulmod(a_2, a_28, R)
                    let var12 := addmod(var10, var11, R)
                    let a_3 := calldataload(0x42c4)
                    let a_29 := calldataload(0x4604)
                    let var13 := mulmod(a_3, a_29, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_54, var15, R)
                    let var17 := mulmod(var9, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_104 := calldataload(0x5b24)
                    let var0 := 0x1
                    let var1 := sub(R, f_104)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_104, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_56 := calldataload(0x4964)
                    let var7 := 0x0
                    let a_4 := calldataload(0x42e4)
                    let a_30 := calldataload(0x4624)
                    let var8 := mulmod(a_4, a_30, R)
                    let var9 := addmod(var7, var8, R)
                    let a_5 := calldataload(0x4304)
                    let a_31 := calldataload(0x4644)
                    let var10 := mulmod(a_5, a_31, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_56, var12, R)
                    let var14 := mulmod(var6, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_106 := calldataload(0x5b64)
                    let var0 := 0x1
                    let var1 := sub(R, f_106)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_106, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_58 := calldataload(0x49a4)
                    let var10 := 0x0
                    let a_6 := calldataload(0x4324)
                    let a_32 := calldataload(0x4664)
                    let var11 := mulmod(a_6, a_32, R)
                    let var12 := addmod(var10, var11, R)
                    let a_7 := calldataload(0x4344)
                    let a_33 := calldataload(0x4684)
                    let var13 := mulmod(a_7, a_33, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_58, var15, R)
                    let var17 := mulmod(var9, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_108 := calldataload(0x5ba4)
                    let var0 := 0x1
                    let var1 := sub(R, f_108)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_108, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_60 := calldataload(0x49e4)
                    let var10 := 0x0
                    let a_8 := calldataload(0x4364)
                    let a_34 := calldataload(0x46a4)
                    let var11 := mulmod(a_8, a_34, R)
                    let var12 := addmod(var10, var11, R)
                    let a_9 := calldataload(0x4384)
                    let a_35 := calldataload(0x46c4)
                    let var13 := mulmod(a_9, a_35, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_60, var15, R)
                    let var17 := mulmod(var9, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_110 := calldataload(0x5be4)
                    let var0 := 0x2
                    let var1 := sub(R, f_110)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_110, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_62 := calldataload(0x4a24)
                    let var7 := 0x0
                    let a_10 := calldataload(0x43a4)
                    let a_36 := calldataload(0x46e4)
                    let var8 := mulmod(a_10, a_36, R)
                    let var9 := addmod(var7, var8, R)
                    let a_11 := calldataload(0x43c4)
                    let a_37 := calldataload(0x4704)
                    let var10 := mulmod(a_11, a_37, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_62, var12, R)
                    let var14 := mulmod(var6, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_111 := calldataload(0x5c04)
                    let var0 := 0x1
                    let var1 := sub(R, f_111)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_111, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_64 := calldataload(0x4a64)
                    let var10 := 0x0
                    let a_12 := calldataload(0x43e4)
                    let a_38 := calldataload(0x4724)
                    let var11 := mulmod(a_12, a_38, R)
                    let var12 := addmod(var10, var11, R)
                    let a_13 := calldataload(0x4404)
                    let a_39 := calldataload(0x4744)
                    let var13 := mulmod(a_13, a_39, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_64, var15, R)
                    let var17 := mulmod(var9, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_113 := calldataload(0x5c44)
                    let var0 := 0x1
                    let var1 := sub(R, f_113)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_113, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_66 := calldataload(0x4aa4)
                    let var10 := 0x0
                    let a_14 := calldataload(0x4424)
                    let a_40 := calldataload(0x4764)
                    let var11 := mulmod(a_14, a_40, R)
                    let var12 := addmod(var10, var11, R)
                    let a_15 := calldataload(0x4444)
                    let a_41 := calldataload(0x4784)
                    let var13 := mulmod(a_15, a_41, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_66, var15, R)
                    let var17 := mulmod(var9, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_115 := calldataload(0x5c84)
                    let var0 := 0x1
                    let var1 := sub(R, f_115)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_115, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_68 := calldataload(0x4ae4)
                    let var10 := 0x0
                    let a_16 := calldataload(0x4464)
                    let a_42 := calldataload(0x47a4)
                    let var11 := mulmod(a_16, a_42, R)
                    let var12 := addmod(var10, var11, R)
                    let a_17 := calldataload(0x4484)
                    let a_43 := calldataload(0x47c4)
                    let var13 := mulmod(a_17, a_43, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_68, var15, R)
                    let var17 := mulmod(var9, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_117 := calldataload(0x5cc4)
                    let var0 := 0x2
                    let var1 := sub(R, f_117)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_117, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_70 := calldataload(0x4b24)
                    let var7 := 0x0
                    let a_18 := calldataload(0x44a4)
                    let a_44 := calldataload(0x47e4)
                    let var8 := mulmod(a_18, a_44, R)
                    let var9 := addmod(var7, var8, R)
                    let a_19 := calldataload(0x44c4)
                    let a_45 := calldataload(0x4804)
                    let var10 := mulmod(a_19, a_45, R)
                    let var11 := addmod(var9, var10, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_70, var12, R)
                    let var14 := mulmod(var6, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_118 := calldataload(0x5ce4)
                    let var0 := 0x1
                    let var1 := sub(R, f_118)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_118, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_72 := calldataload(0x4b64)
                    let var10 := 0x0
                    let a_20 := calldataload(0x44e4)
                    let a_46 := calldataload(0x4824)
                    let var11 := mulmod(a_20, a_46, R)
                    let var12 := addmod(var10, var11, R)
                    let a_21 := calldataload(0x4504)
                    let a_47 := calldataload(0x4844)
                    let var13 := mulmod(a_21, a_47, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_72, var15, R)
                    let var17 := mulmod(var9, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_120 := calldataload(0x5d24)
                    let var0 := 0x1
                    let var1 := sub(R, f_120)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_120, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_74 := calldataload(0x4ba4)
                    let var10 := 0x0
                    let a_22 := calldataload(0x4524)
                    let a_48 := calldataload(0x4864)
                    let var11 := mulmod(a_22, a_48, R)
                    let var12 := addmod(var10, var11, R)
                    let a_23 := calldataload(0x4544)
                    let a_49 := calldataload(0x4884)
                    let var13 := mulmod(a_23, a_49, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_74, var15, R)
                    let var17 := mulmod(var9, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_122 := calldataload(0x5d64)
                    let var0 := 0x1
                    let var1 := sub(R, f_122)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_122, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_76 := calldataload(0x4be4)
                    let var10 := 0x0
                    let a_24 := calldataload(0x4564)
                    let a_50 := calldataload(0x48a4)
                    let var11 := mulmod(a_24, a_50, R)
                    let var12 := addmod(var10, var11, R)
                    let a_25 := calldataload(0x4584)
                    let a_51 := calldataload(0x48c4)
                    let var13 := mulmod(a_25, a_51, R)
                    let var14 := addmod(var12, var13, R)
                    let var15 := sub(R, var14)
                    let var16 := addmod(a_76, var15, R)
                    let var17 := mulmod(var9, var16, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var17, r)
                }
                {
                    let f_96 := calldataload(0x5a24)
                    let var0 := 0x1
                    let var1 := sub(R, f_96)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_96, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_52 := calldataload(0x48e4)
                    let a_26 := calldataload(0x45a4)
                    let var10 := mulmod(var0, a_26, R)
                    let a_27 := calldataload(0x45c4)
                    let var11 := mulmod(var10, a_27, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_52, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_100 := calldataload(0x5aa4)
                    let var0 := 0x1
                    let var1 := sub(R, f_100)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_100, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_54 := calldataload(0x4924)
                    let a_28 := calldataload(0x45e4)
                    let var10 := mulmod(var0, a_28, R)
                    let a_29 := calldataload(0x4604)
                    let var11 := mulmod(var10, a_29, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_54, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_105 := calldataload(0x5b44)
                    let var0 := 0x1
                    let var1 := sub(R, f_105)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_105, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_56 := calldataload(0x4964)
                    let a_30 := calldataload(0x4624)
                    let var7 := mulmod(var0, a_30, R)
                    let a_31 := calldataload(0x4644)
                    let var8 := mulmod(var7, a_31, R)
                    let var9 := sub(R, var8)
                    let var10 := addmod(a_56, var9, R)
                    let var11 := mulmod(var6, var10, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_107 := calldataload(0x5b84)
                    let var0 := 0x1
                    let var1 := sub(R, f_107)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_107, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_58 := calldataload(0x49a4)
                    let a_32 := calldataload(0x4664)
                    let var7 := mulmod(var0, a_32, R)
                    let a_33 := calldataload(0x4684)
                    let var8 := mulmod(var7, a_33, R)
                    let var9 := sub(R, var8)
                    let var10 := addmod(a_58, var9, R)
                    let var11 := mulmod(var6, var10, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_108 := calldataload(0x5ba4)
                    let var0 := 0x1
                    let var1 := sub(R, f_108)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_108, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_60 := calldataload(0x49e4)
                    let a_34 := calldataload(0x46a4)
                    let var10 := mulmod(var0, a_34, R)
                    let a_35 := calldataload(0x46c4)
                    let var11 := mulmod(var10, a_35, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_60, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_111 := calldataload(0x5c04)
                    let var0 := 0x2
                    let var1 := sub(R, f_111)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_111, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_62 := calldataload(0x4a24)
                    let var10 := 0x1
                    let a_36 := calldataload(0x46e4)
                    let var11 := mulmod(var10, a_36, R)
                    let a_37 := calldataload(0x4704)
                    let var12 := mulmod(var11, a_37, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_62, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_112 := calldataload(0x5c24)
                    let var0 := 0x1
                    let var1 := sub(R, f_112)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_112, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_64 := calldataload(0x4a64)
                    let a_38 := calldataload(0x4724)
                    let var7 := mulmod(var0, a_38, R)
                    let a_39 := calldataload(0x4744)
                    let var8 := mulmod(var7, a_39, R)
                    let var9 := sub(R, var8)
                    let var10 := addmod(a_64, var9, R)
                    let var11 := mulmod(var6, var10, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_114 := calldataload(0x5c64)
                    let var0 := 0x1
                    let var1 := sub(R, f_114)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_114, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_66 := calldataload(0x4aa4)
                    let a_40 := calldataload(0x4764)
                    let var7 := mulmod(var0, a_40, R)
                    let a_41 := calldataload(0x4784)
                    let var8 := mulmod(var7, a_41, R)
                    let var9 := sub(R, var8)
                    let var10 := addmod(a_66, var9, R)
                    let var11 := mulmod(var6, var10, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_115 := calldataload(0x5c84)
                    let var0 := 0x1
                    let var1 := sub(R, f_115)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_115, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_68 := calldataload(0x4ae4)
                    let a_42 := calldataload(0x47a4)
                    let var10 := mulmod(var0, a_42, R)
                    let a_43 := calldataload(0x47c4)
                    let var11 := mulmod(var10, a_43, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_68, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_118 := calldataload(0x5ce4)
                    let var0 := 0x2
                    let var1 := sub(R, f_118)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_118, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_70 := calldataload(0x4b24)
                    let var10 := 0x1
                    let a_44 := calldataload(0x47e4)
                    let var11 := mulmod(var10, a_44, R)
                    let a_45 := calldataload(0x4804)
                    let var12 := mulmod(var11, a_45, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_70, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_119 := calldataload(0x5d04)
                    let var0 := 0x1
                    let var1 := sub(R, f_119)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_119, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_72 := calldataload(0x4b64)
                    let a_46 := calldataload(0x4824)
                    let var7 := mulmod(var0, a_46, R)
                    let a_47 := calldataload(0x4844)
                    let var8 := mulmod(var7, a_47, R)
                    let var9 := sub(R, var8)
                    let var10 := addmod(a_72, var9, R)
                    let var11 := mulmod(var6, var10, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_121 := calldataload(0x5d44)
                    let var0 := 0x1
                    let var1 := sub(R, f_121)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_121, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_74 := calldataload(0x4ba4)
                    let a_48 := calldataload(0x4864)
                    let var7 := mulmod(var0, a_48, R)
                    let a_49 := calldataload(0x4884)
                    let var8 := mulmod(var7, a_49, R)
                    let var9 := sub(R, var8)
                    let var10 := addmod(a_74, var9, R)
                    let var11 := mulmod(var6, var10, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var11, r)
                }
                {
                    let f_122 := calldataload(0x5d64)
                    let var0 := 0x1
                    let var1 := sub(R, f_122)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_122, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_76 := calldataload(0x4be4)
                    let a_50 := calldataload(0x48a4)
                    let var10 := mulmod(var0, a_50, R)
                    let a_51 := calldataload(0x48c4)
                    let var11 := mulmod(var10, a_51, R)
                    let var12 := sub(R, var11)
                    let var13 := addmod(a_76, var12, R)
                    let var14 := mulmod(var9, var13, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_103 := calldataload(0x5b04)
                    let var0 := 0x1
                    let var1 := sub(R, f_103)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_103, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_52 := calldataload(0x48e4)
                    let a_52_prev_1 := calldataload(0x4c84)
                    let a_26 := calldataload(0x45a4)
                    let var7 := mulmod(var0, a_26, R)
                    let a_27 := calldataload(0x45c4)
                    let var8 := mulmod(var7, a_27, R)
                    let var9 := mulmod(a_52_prev_1, var8, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_52, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_104 := calldataload(0x5b24)
                    let var0 := 0x2
                    let var1 := sub(R, f_104)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_104, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_54 := calldataload(0x4924)
                    let a_54_prev_1 := calldataload(0x4ca4)
                    let var7 := 0x1
                    let a_28 := calldataload(0x45e4)
                    let var8 := mulmod(var7, a_28, R)
                    let a_29 := calldataload(0x4604)
                    let var9 := mulmod(var8, a_29, R)
                    let var10 := mulmod(a_54_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_54, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_105 := calldataload(0x5b44)
                    let var0 := 0x1
                    let var1 := sub(R, f_105)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_105, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_56 := calldataload(0x4964)
                    let a_56_prev_1 := calldataload(0x4cc4)
                    let a_30 := calldataload(0x4624)
                    let var7 := mulmod(var0, a_30, R)
                    let a_31 := calldataload(0x4644)
                    let var8 := mulmod(var7, a_31, R)
                    let var9 := mulmod(a_56_prev_1, var8, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_56, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_107 := calldataload(0x5b84)
                    let var0 := 0x2
                    let var1 := sub(R, f_107)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_107, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_58 := calldataload(0x49a4)
                    let a_58_prev_1 := calldataload(0x4ce4)
                    let var7 := 0x1
                    let a_32 := calldataload(0x4664)
                    let var8 := mulmod(var7, a_32, R)
                    let a_33 := calldataload(0x4684)
                    let var9 := mulmod(var8, a_33, R)
                    let var10 := mulmod(a_58_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_58, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_109 := calldataload(0x5bc4)
                    let var0 := 0x2
                    let var1 := sub(R, f_109)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_109, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_60 := calldataload(0x49e4)
                    let a_60_prev_1 := calldataload(0x4d04)
                    let var7 := 0x1
                    let a_34 := calldataload(0x46a4)
                    let var8 := mulmod(var7, a_34, R)
                    let a_35 := calldataload(0x46c4)
                    let var9 := mulmod(var8, a_35, R)
                    let var10 := mulmod(a_60_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_60, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_110 := calldataload(0x5be4)
                    let var0 := 0x1
                    let var1 := sub(R, f_110)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_110, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_62 := calldataload(0x4a24)
                    let a_62_prev_1 := calldataload(0x4d24)
                    let a_36 := calldataload(0x46e4)
                    let var7 := mulmod(var0, a_36, R)
                    let a_37 := calldataload(0x4704)
                    let var8 := mulmod(var7, a_37, R)
                    let var9 := mulmod(a_62_prev_1, var8, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_62, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_112 := calldataload(0x5c24)
                    let var0 := 0x1
                    let var1 := sub(R, f_112)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_112, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_64 := calldataload(0x4a64)
                    let a_64_prev_1 := calldataload(0x4d44)
                    let a_38 := calldataload(0x4724)
                    let var7 := mulmod(var0, a_38, R)
                    let a_39 := calldataload(0x4744)
                    let var8 := mulmod(var7, a_39, R)
                    let var9 := mulmod(a_64_prev_1, var8, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_64, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_114 := calldataload(0x5c64)
                    let var0 := 0x2
                    let var1 := sub(R, f_114)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_114, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_66 := calldataload(0x4aa4)
                    let a_66_prev_1 := calldataload(0x4d64)
                    let var7 := 0x1
                    let a_40 := calldataload(0x4764)
                    let var8 := mulmod(var7, a_40, R)
                    let a_41 := calldataload(0x4784)
                    let var9 := mulmod(var8, a_41, R)
                    let var10 := mulmod(a_66_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_66, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_116 := calldataload(0x5ca4)
                    let var0 := 0x2
                    let var1 := sub(R, f_116)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_116, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_68 := calldataload(0x4ae4)
                    let a_68_prev_1 := calldataload(0x4d84)
                    let var7 := 0x1
                    let a_42 := calldataload(0x47a4)
                    let var8 := mulmod(var7, a_42, R)
                    let a_43 := calldataload(0x47c4)
                    let var9 := mulmod(var8, a_43, R)
                    let var10 := mulmod(a_68_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_68, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_117 := calldataload(0x5cc4)
                    let var0 := 0x1
                    let var1 := sub(R, f_117)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_117, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_70 := calldataload(0x4b24)
                    let a_70_prev_1 := calldataload(0x4da4)
                    let a_44 := calldataload(0x47e4)
                    let var7 := mulmod(var0, a_44, R)
                    let a_45 := calldataload(0x4804)
                    let var8 := mulmod(var7, a_45, R)
                    let var9 := mulmod(a_70_prev_1, var8, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_70, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_119 := calldataload(0x5d04)
                    let var0 := 0x1
                    let var1 := sub(R, f_119)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_119, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_72 := calldataload(0x4b64)
                    let a_72_prev_1 := calldataload(0x4dc4)
                    let a_46 := calldataload(0x4824)
                    let var7 := mulmod(var0, a_46, R)
                    let a_47 := calldataload(0x4844)
                    let var8 := mulmod(var7, a_47, R)
                    let var9 := mulmod(a_72_prev_1, var8, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_72, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_121 := calldataload(0x5d44)
                    let var0 := 0x2
                    let var1 := sub(R, f_121)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_121, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_74 := calldataload(0x4ba4)
                    let a_74_prev_1 := calldataload(0x4de4)
                    let var7 := 0x1
                    let a_48 := calldataload(0x4864)
                    let var8 := mulmod(var7, a_48, R)
                    let a_49 := calldataload(0x4884)
                    let var9 := mulmod(var8, a_49, R)
                    let var10 := mulmod(a_74_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_74, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_123 := calldataload(0x5d84)
                    let var0 := 0x2
                    let var1 := sub(R, f_123)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_123, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_76 := calldataload(0x4be4)
                    let a_76_prev_1 := calldataload(0x4e04)
                    let var7 := 0x1
                    let a_50 := calldataload(0x48a4)
                    let var8 := mulmod(var7, a_50, R)
                    let a_51 := calldataload(0x48c4)
                    let var9 := mulmod(var8, a_51, R)
                    let var10 := mulmod(a_76_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_76, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_98 := calldataload(0x5a64)
                    let var0 := 0x1
                    let var1 := sub(R, f_98)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_98, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_52 := calldataload(0x48e4)
                    let var10 := 0x0
                    let a_26 := calldataload(0x45a4)
                    let var11 := addmod(var10, a_26, R)
                    let a_27 := calldataload(0x45c4)
                    let var12 := addmod(var11, a_27, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_52, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_104 := calldataload(0x5b24)
                    let var0 := 0x1
                    let var1 := sub(R, f_104)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_104, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_54 := calldataload(0x4924)
                    let var7 := 0x0
                    let a_28 := calldataload(0x45e4)
                    let var8 := addmod(var7, a_28, R)
                    let a_29 := calldataload(0x4604)
                    let var9 := addmod(var8, a_29, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_54, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_106 := calldataload(0x5b64)
                    let var0 := 0x1
                    let var1 := sub(R, f_106)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_106, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_56 := calldataload(0x4964)
                    let var10 := 0x0
                    let a_30 := calldataload(0x4624)
                    let var11 := addmod(var10, a_30, R)
                    let a_31 := calldataload(0x4644)
                    let var12 := addmod(var11, a_31, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_56, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_108 := calldataload(0x5ba4)
                    let var0 := 0x2
                    let var1 := sub(R, f_108)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_108, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_58 := calldataload(0x49a4)
                    let var10 := 0x0
                    let a_32 := calldataload(0x4664)
                    let var11 := addmod(var10, a_32, R)
                    let a_33 := calldataload(0x4684)
                    let var12 := addmod(var11, a_33, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_58, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_109 := calldataload(0x5bc4)
                    let var0 := 0x1
                    let var1 := sub(R, f_109)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_109, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_60 := calldataload(0x49e4)
                    let var7 := 0x0
                    let a_34 := calldataload(0x46a4)
                    let var8 := addmod(var7, a_34, R)
                    let a_35 := calldataload(0x46c4)
                    let var9 := addmod(var8, a_35, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_60, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_111 := calldataload(0x5c04)
                    let var0 := 0x1
                    let var1 := sub(R, f_111)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_111, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_62 := calldataload(0x4a24)
                    let var10 := 0x0
                    let a_36 := calldataload(0x46e4)
                    let var11 := addmod(var10, a_36, R)
                    let a_37 := calldataload(0x4704)
                    let var12 := addmod(var11, a_37, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_62, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_113 := calldataload(0x5c44)
                    let var0 := 0x1
                    let var1 := sub(R, f_113)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_113, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_64 := calldataload(0x4a64)
                    let var10 := 0x0
                    let a_38 := calldataload(0x4724)
                    let var11 := addmod(var10, a_38, R)
                    let a_39 := calldataload(0x4744)
                    let var12 := addmod(var11, a_39, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_64, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_115 := calldataload(0x5c84)
                    let var0 := 0x2
                    let var1 := sub(R, f_115)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_115, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_66 := calldataload(0x4aa4)
                    let var10 := 0x0
                    let a_40 := calldataload(0x4764)
                    let var11 := addmod(var10, a_40, R)
                    let a_41 := calldataload(0x4784)
                    let var12 := addmod(var11, a_41, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_66, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_116 := calldataload(0x5ca4)
                    let var0 := 0x1
                    let var1 := sub(R, f_116)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_116, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_68 := calldataload(0x4ae4)
                    let var7 := 0x0
                    let a_42 := calldataload(0x47a4)
                    let var8 := addmod(var7, a_42, R)
                    let a_43 := calldataload(0x47c4)
                    let var9 := addmod(var8, a_43, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_68, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_118 := calldataload(0x5ce4)
                    let var0 := 0x1
                    let var1 := sub(R, f_118)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_118, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_70 := calldataload(0x4b24)
                    let var10 := 0x0
                    let a_44 := calldataload(0x47e4)
                    let var11 := addmod(var10, a_44, R)
                    let a_45 := calldataload(0x4804)
                    let var12 := addmod(var11, a_45, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_70, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_120 := calldataload(0x5d24)
                    let var0 := 0x1
                    let var1 := sub(R, f_120)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_120, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_72 := calldataload(0x4b64)
                    let var10 := 0x0
                    let a_46 := calldataload(0x4824)
                    let var11 := addmod(var10, a_46, R)
                    let a_47 := calldataload(0x4844)
                    let var12 := addmod(var11, a_47, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_72, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_122 := calldataload(0x5d64)
                    let var0 := 0x2
                    let var1 := sub(R, f_122)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_122, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_74 := calldataload(0x4ba4)
                    let var10 := 0x0
                    let a_48 := calldataload(0x4864)
                    let var11 := addmod(var10, a_48, R)
                    let a_49 := calldataload(0x4884)
                    let var12 := addmod(var11, a_49, R)
                    let var13 := sub(R, var12)
                    let var14 := addmod(a_74, var13, R)
                    let var15 := mulmod(var9, var14, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_123 := calldataload(0x5d84)
                    let var0 := 0x1
                    let var1 := sub(R, f_123)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_123, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_76 := calldataload(0x4be4)
                    let var7 := 0x0
                    let a_50 := calldataload(0x48a4)
                    let var8 := addmod(var7, a_50, R)
                    let a_51 := calldataload(0x48c4)
                    let var9 := addmod(var8, a_51, R)
                    let var10 := sub(R, var9)
                    let var11 := addmod(a_76, var10, R)
                    let var12 := mulmod(var6, var11, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_97 := calldataload(0x5a44)
                    let var0 := 0x1
                    let var1 := sub(R, f_97)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_97, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_52 := calldataload(0x48e4)
                    let a_52_prev_1 := calldataload(0x4c84)
                    let var10 := 0x0
                    let a_26 := calldataload(0x45a4)
                    let var11 := addmod(var10, a_26, R)
                    let a_27 := calldataload(0x45c4)
                    let var12 := addmod(var11, a_27, R)
                    let var13 := addmod(a_52_prev_1, var12, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_52, var14, R)
                    let var16 := mulmod(var9, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_102 := calldataload(0x5ae4)
                    let var0 := 0x1
                    let var1 := sub(R, f_102)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_102, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_54 := calldataload(0x4924)
                    let a_54_prev_1 := calldataload(0x4ca4)
                    let var10 := 0x0
                    let a_28 := calldataload(0x45e4)
                    let var11 := addmod(var10, a_28, R)
                    let a_29 := calldataload(0x4604)
                    let var12 := addmod(var11, a_29, R)
                    let var13 := addmod(a_54_prev_1, var12, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_54, var14, R)
                    let var16 := mulmod(var9, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_106 := calldataload(0x5b64)
                    let var0 := 0x2
                    let var1 := sub(R, f_106)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_106, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_56 := calldataload(0x4964)
                    let a_56_prev_1 := calldataload(0x4cc4)
                    let var10 := 0x0
                    let a_30 := calldataload(0x4624)
                    let var11 := addmod(var10, a_30, R)
                    let a_31 := calldataload(0x4644)
                    let var12 := addmod(var11, a_31, R)
                    let var13 := addmod(a_56_prev_1, var12, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_56, var14, R)
                    let var16 := mulmod(var9, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_107 := calldataload(0x5b84)
                    let var0 := 0x1
                    let var1 := sub(R, f_107)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_107, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_58 := calldataload(0x49a4)
                    let a_58_prev_1 := calldataload(0x4ce4)
                    let var7 := 0x0
                    let a_32 := calldataload(0x4664)
                    let var8 := addmod(var7, a_32, R)
                    let a_33 := calldataload(0x4684)
                    let var9 := addmod(var8, a_33, R)
                    let var10 := addmod(a_58_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_58, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_109 := calldataload(0x5bc4)
                    let var0 := 0x1
                    let var1 := sub(R, f_109)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_109, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_60 := calldataload(0x49e4)
                    let a_60_prev_1 := calldataload(0x4d04)
                    let var7 := 0x0
                    let a_34 := calldataload(0x46a4)
                    let var8 := addmod(var7, a_34, R)
                    let a_35 := calldataload(0x46c4)
                    let var9 := addmod(var8, a_35, R)
                    let var10 := addmod(a_60_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_60, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_111 := calldataload(0x5c04)
                    let var0 := 0x1
                    let var1 := sub(R, f_111)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_111, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_62 := calldataload(0x4a24)
                    let a_62_prev_1 := calldataload(0x4d24)
                    let var10 := 0x0
                    let a_36 := calldataload(0x46e4)
                    let var11 := addmod(var10, a_36, R)
                    let a_37 := calldataload(0x4704)
                    let var12 := addmod(var11, a_37, R)
                    let var13 := addmod(a_62_prev_1, var12, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_62, var14, R)
                    let var16 := mulmod(var9, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_113 := calldataload(0x5c44)
                    let var0 := 0x2
                    let var1 := sub(R, f_113)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_113, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_64 := calldataload(0x4a64)
                    let a_64_prev_1 := calldataload(0x4d44)
                    let var10 := 0x0
                    let a_38 := calldataload(0x4724)
                    let var11 := addmod(var10, a_38, R)
                    let a_39 := calldataload(0x4744)
                    let var12 := addmod(var11, a_39, R)
                    let var13 := addmod(a_64_prev_1, var12, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_64, var14, R)
                    let var16 := mulmod(var9, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_114 := calldataload(0x5c64)
                    let var0 := 0x1
                    let var1 := sub(R, f_114)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_114, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_66 := calldataload(0x4aa4)
                    let a_66_prev_1 := calldataload(0x4d64)
                    let var7 := 0x0
                    let a_40 := calldataload(0x4764)
                    let var8 := addmod(var7, a_40, R)
                    let a_41 := calldataload(0x4784)
                    let var9 := addmod(var8, a_41, R)
                    let var10 := addmod(a_66_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_66, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_116 := calldataload(0x5ca4)
                    let var0 := 0x1
                    let var1 := sub(R, f_116)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_116, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_68 := calldataload(0x4ae4)
                    let a_68_prev_1 := calldataload(0x4d84)
                    let var7 := 0x0
                    let a_42 := calldataload(0x47a4)
                    let var8 := addmod(var7, a_42, R)
                    let a_43 := calldataload(0x47c4)
                    let var9 := addmod(var8, a_43, R)
                    let var10 := addmod(a_68_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_68, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_118 := calldataload(0x5ce4)
                    let var0 := 0x1
                    let var1 := sub(R, f_118)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_118, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_70 := calldataload(0x4b24)
                    let a_70_prev_1 := calldataload(0x4da4)
                    let var10 := 0x0
                    let a_44 := calldataload(0x47e4)
                    let var11 := addmod(var10, a_44, R)
                    let a_45 := calldataload(0x4804)
                    let var12 := addmod(var11, a_45, R)
                    let var13 := addmod(a_70_prev_1, var12, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_70, var14, R)
                    let var16 := mulmod(var9, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_120 := calldataload(0x5d24)
                    let var0 := 0x2
                    let var1 := sub(R, f_120)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_120, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, R)
                    let var9 := mulmod(var6, var8, R)
                    let a_72 := calldataload(0x4b64)
                    let a_72_prev_1 := calldataload(0x4dc4)
                    let var10 := 0x0
                    let a_46 := calldataload(0x4824)
                    let var11 := addmod(var10, a_46, R)
                    let a_47 := calldataload(0x4844)
                    let var12 := addmod(var11, a_47, R)
                    let var13 := addmod(a_72_prev_1, var12, R)
                    let var14 := sub(R, var13)
                    let var15 := addmod(a_72, var14, R)
                    let var16 := mulmod(var9, var15, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var16, r)
                }
                {
                    let f_121 := calldataload(0x5d44)
                    let var0 := 0x1
                    let var1 := sub(R, f_121)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_121, var2, R)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_74 := calldataload(0x4ba4)
                    let a_74_prev_1 := calldataload(0x4de4)
                    let var7 := 0x0
                    let a_48 := calldataload(0x4864)
                    let var8 := addmod(var7, a_48, R)
                    let a_49 := calldataload(0x4884)
                    let var9 := addmod(var8, a_49, R)
                    let var10 := addmod(a_74_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_74, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_123 := calldataload(0x5d84)
                    let var0 := 0x1
                    let var1 := sub(R, f_123)
                    let var2 := addmod(var0, var1, R)
                    let var3 := mulmod(f_123, var2, R)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, R)
                    let var6 := mulmod(var3, var5, R)
                    let a_76 := calldataload(0x4be4)
                    let a_76_prev_1 := calldataload(0x4e04)
                    let var7 := 0x0
                    let a_50 := calldataload(0x48a4)
                    let var8 := addmod(var7, a_50, R)
                    let a_51 := calldataload(0x48c4)
                    let var9 := addmod(var8, a_51, R)
                    let var10 := addmod(a_76_prev_1, var9, R)
                    let var11 := sub(R, var10)
                    let var12 := addmod(a_76, var11, R)
                    let var13 := mulmod(var6, var12, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_3 := calldataload(0x4e84)
                    let var0 := 0x0
                    let var1 := mulmod(f_3, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_4 := calldataload(0x4ea4)
                    let var0 := 0x0
                    let var1 := mulmod(f_4, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_5 := calldataload(0x4ec4)
                    let var0 := 0x0
                    let var1 := mulmod(f_5, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_6 := calldataload(0x4ee4)
                    let var0 := 0x0
                    let var1 := mulmod(f_6, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_7 := calldataload(0x4f04)
                    let var0 := 0x0
                    let var1 := mulmod(f_7, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_8 := calldataload(0x4f24)
                    let var0 := 0x0
                    let var1 := mulmod(f_8, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_9 := calldataload(0x4f44)
                    let var0 := 0x0
                    let var1 := mulmod(f_9, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_10 := calldataload(0x4f64)
                    let var0 := 0x0
                    let var1 := mulmod(f_10, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_11 := calldataload(0x4f84)
                    let var0 := 0x0
                    let var1 := mulmod(f_11, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_12 := calldataload(0x4fa4)
                    let var0 := 0x0
                    let var1 := mulmod(f_12, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_13 := calldataload(0x4fc4)
                    let var0 := 0x0
                    let var1 := mulmod(f_13, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_14 := calldataload(0x4fe4)
                    let var0 := 0x0
                    let var1 := mulmod(f_14, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_15 := calldataload(0x5004)
                    let var0 := 0x0
                    let var1 := mulmod(f_15, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_16 := calldataload(0x5024)
                    let var0 := 0x0
                    let var1 := mulmod(f_16, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_17 := calldataload(0x5044)
                    let var0 := 0x0
                    let var1 := mulmod(f_17, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_18 := calldataload(0x5064)
                    let var0 := 0x0
                    let var1 := mulmod(f_18, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_19 := calldataload(0x5084)
                    let var0 := 0x0
                    let var1 := mulmod(f_19, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_20 := calldataload(0x50a4)
                    let var0 := 0x0
                    let var1 := mulmod(f_20, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_21 := calldataload(0x50c4)
                    let var0 := 0x0
                    let var1 := mulmod(f_21, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_22 := calldataload(0x50e4)
                    let var0 := 0x0
                    let var1 := mulmod(f_22, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_23 := calldataload(0x5104)
                    let var0 := 0x0
                    let var1 := mulmod(f_23, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_24 := calldataload(0x5124)
                    let var0 := 0x0
                    let var1 := mulmod(f_24, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_25 := calldataload(0x5144)
                    let var0 := 0x0
                    let var1 := mulmod(f_25, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_26 := calldataload(0x5164)
                    let var0 := 0x0
                    let var1 := mulmod(f_26, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_27 := calldataload(0x5184)
                    let var0 := 0x0
                    let var1 := mulmod(f_27, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_28 := calldataload(0x51a4)
                    let var0 := 0x0
                    let var1 := mulmod(f_28, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_29 := calldataload(0x51c4)
                    let var0 := 0x0
                    let var1 := mulmod(f_29, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_30 := calldataload(0x51e4)
                    let var0 := 0x0
                    let var1 := mulmod(f_30, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_31 := calldataload(0x5204)
                    let var0 := 0x0
                    let var1 := mulmod(f_31, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_32 := calldataload(0x5224)
                    let var0 := 0x0
                    let var1 := mulmod(f_32, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_33 := calldataload(0x5244)
                    let var0 := 0x0
                    let var1 := mulmod(f_33, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_34 := calldataload(0x5264)
                    let var0 := 0x0
                    let var1 := mulmod(f_34, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_35 := calldataload(0x5284)
                    let var0 := 0x0
                    let var1 := mulmod(f_35, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_36 := calldataload(0x52a4)
                    let var0 := 0x0
                    let var1 := mulmod(f_36, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_37 := calldataload(0x52c4)
                    let var0 := 0x0
                    let var1 := mulmod(f_37, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_38 := calldataload(0x52e4)
                    let var0 := 0x0
                    let var1 := mulmod(f_38, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_39 := calldataload(0x5304)
                    let var0 := 0x0
                    let var1 := mulmod(f_39, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_40 := calldataload(0x5324)
                    let var0 := 0x0
                    let var1 := mulmod(f_40, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_41 := calldataload(0x5344)
                    let var0 := 0x0
                    let var1 := mulmod(f_41, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_42 := calldataload(0x5364)
                    let var0 := 0x0
                    let var1 := mulmod(f_42, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_43 := calldataload(0x5384)
                    let var0 := 0x0
                    let var1 := mulmod(f_43, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_44 := calldataload(0x53a4)
                    let var0 := 0x0
                    let var1 := mulmod(f_44, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_45 := calldataload(0x53c4)
                    let var0 := 0x0
                    let var1 := mulmod(f_45, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_46 := calldataload(0x53e4)
                    let var0 := 0x0
                    let var1 := mulmod(f_46, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_47 := calldataload(0x5404)
                    let var0 := 0x0
                    let var1 := mulmod(f_47, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_48 := calldataload(0x5424)
                    let var0 := 0x0
                    let var1 := mulmod(f_48, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_49 := calldataload(0x5444)
                    let var0 := 0x0
                    let var1 := mulmod(f_49, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_50 := calldataload(0x5464)
                    let var0 := 0x0
                    let var1 := mulmod(f_50, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_51 := calldataload(0x5484)
                    let var0 := 0x0
                    let var1 := mulmod(f_51, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_52 := calldataload(0x54a4)
                    let var0 := 0x0
                    let var1 := mulmod(f_52, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_53 := calldataload(0x54c4)
                    let var0 := 0x0
                    let var1 := mulmod(f_53, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let f_54 := calldataload(0x54e4)
                    let var0 := 0x0
                    let var1 := mulmod(f_54, var0, R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var1, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := addmod(l_0, sub(R, mulmod(l_0, calldataload(0x6824), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let perm_z_last := calldataload(0x6fa4)
                    let eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(perm_z_last, perm_z_last, R), sub(R, perm_z_last), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6884), sub(R, calldataload(0x6864)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x68e4), sub(R, calldataload(0x68c4)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6944), sub(R, calldataload(0x6924)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x69a4), sub(R, calldataload(0x6984)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6a04), sub(R, calldataload(0x69e4)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6a64), sub(R, calldataload(0x6a44)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6ac4), sub(R, calldataload(0x6aa4)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6b24), sub(R, calldataload(0x6b04)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6b84), sub(R, calldataload(0x6b64)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6be4), sub(R, calldataload(0x6bc4)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6c44), sub(R, calldataload(0x6c24)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6ca4), sub(R, calldataload(0x6c84)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6d04), sub(R, calldataload(0x6ce4)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6d64), sub(R, calldataload(0x6d44)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6dc4), sub(R, calldataload(0x6da4)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6e24), sub(R, calldataload(0x6e04)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6e84), sub(R, calldataload(0x6e64)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6ee4), sub(R, calldataload(0x6ec4)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6f44), sub(R, calldataload(0x6f24)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x6fa4), sub(R, calldataload(0x6f84)), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6844)
                    let rhs := calldataload(0x6824)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4264), mulmod(beta, calldataload(0x5dc4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4284), mulmod(beta, calldataload(0x5de4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x42a4), mulmod(beta, calldataload(0x5e04), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x42c4), mulmod(beta, calldataload(0x5e24), R), R), gamma, R), R)
                    mstore(0x00, mulmod(beta, mload(X_MPTR), R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4264), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4284), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x42a4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x42c4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x68a4)
                    let rhs := calldataload(0x6884)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x42e4), mulmod(beta, calldataload(0x5e44), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4304), mulmod(beta, calldataload(0x5e64), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4324), mulmod(beta, calldataload(0x5e84), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4344), mulmod(beta, calldataload(0x5ea4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x42e4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4304), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4324), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4344), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6904)
                    let rhs := calldataload(0x68e4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4364), mulmod(beta, calldataload(0x5ec4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4384), mulmod(beta, calldataload(0x5ee4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x43a4), mulmod(beta, calldataload(0x5f04), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x43c4), mulmod(beta, calldataload(0x5f24), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4364), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4384), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x43a4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x43c4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6964)
                    let rhs := calldataload(0x6944)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x43e4), mulmod(beta, calldataload(0x5f44), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4404), mulmod(beta, calldataload(0x5f64), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4424), mulmod(beta, calldataload(0x5f84), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4444), mulmod(beta, calldataload(0x5fa4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x43e4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4404), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4424), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4444), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x69c4)
                    let rhs := calldataload(0x69a4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4464), mulmod(beta, calldataload(0x5fc4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4484), mulmod(beta, calldataload(0x5fe4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x44a4), mulmod(beta, calldataload(0x6004), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x44c4), mulmod(beta, calldataload(0x6024), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4464), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4484), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x44a4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x44c4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6a24)
                    let rhs := calldataload(0x6a04)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x44e4), mulmod(beta, calldataload(0x6044), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4504), mulmod(beta, calldataload(0x6064), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4524), mulmod(beta, calldataload(0x6084), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4544), mulmod(beta, calldataload(0x60a4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x44e4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4504), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4524), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4544), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6a84)
                    let rhs := calldataload(0x6a64)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4564), mulmod(beta, calldataload(0x60c4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4584), mulmod(beta, calldataload(0x60e4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x45a4), mulmod(beta, calldataload(0x6104), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x45c4), mulmod(beta, calldataload(0x6124), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4564), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4584), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x45a4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x45c4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6ae4)
                    let rhs := calldataload(0x6ac4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x45e4), mulmod(beta, calldataload(0x6144), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4604), mulmod(beta, calldataload(0x6164), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4624), mulmod(beta, calldataload(0x6184), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4644), mulmod(beta, calldataload(0x61a4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x45e4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4604), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4624), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4644), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6b44)
                    let rhs := calldataload(0x6b24)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4664), mulmod(beta, calldataload(0x61c4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4684), mulmod(beta, calldataload(0x61e4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x46a4), mulmod(beta, calldataload(0x6204), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x46c4), mulmod(beta, calldataload(0x6224), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4664), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4684), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x46a4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x46c4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6ba4)
                    let rhs := calldataload(0x6b84)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x46e4), mulmod(beta, calldataload(0x6244), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4704), mulmod(beta, calldataload(0x6264), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4724), mulmod(beta, calldataload(0x6284), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4744), mulmod(beta, calldataload(0x62a4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x46e4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4704), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4724), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4744), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6c04)
                    let rhs := calldataload(0x6be4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4764), mulmod(beta, calldataload(0x62c4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4784), mulmod(beta, calldataload(0x62e4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x47a4), mulmod(beta, calldataload(0x6304), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x47c4), mulmod(beta, calldataload(0x6324), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4764), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4784), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x47a4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x47c4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6c64)
                    let rhs := calldataload(0x6c44)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x47e4), mulmod(beta, calldataload(0x6344), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4804), mulmod(beta, calldataload(0x6364), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4824), mulmod(beta, calldataload(0x6384), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4844), mulmod(beta, calldataload(0x63a4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x47e4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4804), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4824), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4844), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6cc4)
                    let rhs := calldataload(0x6ca4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4864), mulmod(beta, calldataload(0x63c4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4884), mulmod(beta, calldataload(0x63e4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x48a4), mulmod(beta, calldataload(0x6404), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x48c4), mulmod(beta, calldataload(0x6424), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4864), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4884), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x48a4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x48c4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6d24)
                    let rhs := calldataload(0x6d04)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x48e4), mulmod(beta, calldataload(0x6444), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4904), mulmod(beta, calldataload(0x6464), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4924), mulmod(beta, calldataload(0x6484), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4944), mulmod(beta, calldataload(0x64a4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x48e4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4904), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4924), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4944), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6d84)
                    let rhs := calldataload(0x6d64)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4964), mulmod(beta, calldataload(0x64c4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4984), mulmod(beta, calldataload(0x64e4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x49a4), mulmod(beta, calldataload(0x6504), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x49c4), mulmod(beta, calldataload(0x6524), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4964), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4984), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x49a4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x49c4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6de4)
                    let rhs := calldataload(0x6dc4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x49e4), mulmod(beta, calldataload(0x6544), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4a04), mulmod(beta, calldataload(0x6564), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4a24), mulmod(beta, calldataload(0x6584), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4a44), mulmod(beta, calldataload(0x65a4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x49e4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4a04), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4a24), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4a44), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6e44)
                    let rhs := calldataload(0x6e24)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4a64), mulmod(beta, calldataload(0x65c4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4a84), mulmod(beta, calldataload(0x65e4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4aa4), mulmod(beta, calldataload(0x6604), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4ac4), mulmod(beta, calldataload(0x6624), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4a64), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4a84), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4aa4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4ac4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6ea4)
                    let rhs := calldataload(0x6e84)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4ae4), mulmod(beta, calldataload(0x6644), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4b04), mulmod(beta, calldataload(0x6664), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4b24), mulmod(beta, calldataload(0x6684), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4b44), mulmod(beta, calldataload(0x66a4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4ae4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4b04), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4b24), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4b44), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6f04)
                    let rhs := calldataload(0x6ee4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4b64), mulmod(beta, calldataload(0x66c4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4b84), mulmod(beta, calldataload(0x66e4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4ba4), mulmod(beta, calldataload(0x6704), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4bc4), mulmod(beta, calldataload(0x6724), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4b64), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4b84), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4ba4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4bc4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6f64)
                    let rhs := calldataload(0x6f44)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4be4), mulmod(beta, calldataload(0x6744), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4c04), mulmod(beta, calldataload(0x6764), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4c24), mulmod(beta, calldataload(0x6784), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4c44), mulmod(beta, calldataload(0x67a4), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4be4), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4c04), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4c24), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4c44), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x6fc4)
                    let rhs := calldataload(0x6fa4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4c64), mulmod(beta, calldataload(0x67c4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x4e24), mulmod(beta, calldataload(0x67e4), R), R), gamma, R), R)
                    lhs := mulmod(lhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mulmod(beta, calldataload(0x6804), R), R), gamma, R), R)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4c64), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x4e24), mload(0x00), R), gamma, R), R)
                    mstore(0x00, mulmod(mload(0x00), DELTA, R))
                    rhs := mulmod(rhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mload(0x00), R), gamma, R), R)
                    let left_sub_right := addmod(lhs, sub(R, rhs), R)
                    let eval := addmod(left_sub_right, sub(R, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), R), R)), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x6fe4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x6fe4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_56 := calldataload(0x5524)
                        let var1 := mulmod(var0, f_56, R)
                        let a_0 := calldataload(0x4264)
                        let var2 := mulmod(a_0, f_56, R)
                        let a_26 := calldataload(0x45a4)
                        let var3 := mulmod(a_26, f_56, R)
                        let a_52 := calldataload(0x48e4)
                        let var4 := mulmod(a_52, f_56, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7024), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7004), sub(R, calldataload(0x6fe4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7044), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7044), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_57 := calldataload(0x5544)
                        let var1 := mulmod(var0, f_57, R)
                        let a_1 := calldataload(0x4284)
                        let var2 := mulmod(a_1, f_57, R)
                        let a_27 := calldataload(0x45c4)
                        let var3 := mulmod(a_27, f_57, R)
                        let a_53 := calldataload(0x4904)
                        let var4 := mulmod(a_53, f_57, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7084), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7064), sub(R, calldataload(0x7044)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x70a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x70a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_58 := calldataload(0x5564)
                        let var1 := mulmod(var0, f_58, R)
                        let a_2 := calldataload(0x42a4)
                        let var2 := mulmod(a_2, f_58, R)
                        let a_28 := calldataload(0x45e4)
                        let var3 := mulmod(a_28, f_58, R)
                        let a_54 := calldataload(0x4924)
                        let var4 := mulmod(a_54, f_58, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x70e4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x70c4), sub(R, calldataload(0x70a4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7104), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7104), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_59 := calldataload(0x5584)
                        let var1 := mulmod(var0, f_59, R)
                        let a_3 := calldataload(0x42c4)
                        let var2 := mulmod(a_3, f_59, R)
                        let a_29 := calldataload(0x4604)
                        let var3 := mulmod(a_29, f_59, R)
                        let a_55 := calldataload(0x4944)
                        let var4 := mulmod(a_55, f_59, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7144), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7124), sub(R, calldataload(0x7104)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7164), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7164), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_60 := calldataload(0x55a4)
                        let var1 := mulmod(var0, f_60, R)
                        let a_4 := calldataload(0x42e4)
                        let var2 := mulmod(a_4, f_60, R)
                        let a_30 := calldataload(0x4624)
                        let var3 := mulmod(a_30, f_60, R)
                        let a_56 := calldataload(0x4964)
                        let var4 := mulmod(a_56, f_60, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x71a4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7184), sub(R, calldataload(0x7164)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x71c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x71c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_61 := calldataload(0x55c4)
                        let var1 := mulmod(var0, f_61, R)
                        let a_5 := calldataload(0x4304)
                        let var2 := mulmod(a_5, f_61, R)
                        let a_31 := calldataload(0x4644)
                        let var3 := mulmod(a_31, f_61, R)
                        let a_57 := calldataload(0x4984)
                        let var4 := mulmod(a_57, f_61, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7204), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x71e4), sub(R, calldataload(0x71c4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7224), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7224), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_62 := calldataload(0x55e4)
                        let var1 := mulmod(var0, f_62, R)
                        let a_6 := calldataload(0x4324)
                        let var2 := mulmod(a_6, f_62, R)
                        let a_32 := calldataload(0x4664)
                        let var3 := mulmod(a_32, f_62, R)
                        let a_58 := calldataload(0x49a4)
                        let var4 := mulmod(a_58, f_62, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7264), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7244), sub(R, calldataload(0x7224)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7284), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7284), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_63 := calldataload(0x5604)
                        let var1 := mulmod(var0, f_63, R)
                        let a_7 := calldataload(0x4344)
                        let var2 := mulmod(a_7, f_63, R)
                        let a_33 := calldataload(0x4684)
                        let var3 := mulmod(a_33, f_63, R)
                        let a_59 := calldataload(0x49c4)
                        let var4 := mulmod(a_59, f_63, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x72c4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x72a4), sub(R, calldataload(0x7284)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x72e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x72e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_64 := calldataload(0x5624)
                        let var1 := mulmod(var0, f_64, R)
                        let a_8 := calldataload(0x4364)
                        let var2 := mulmod(a_8, f_64, R)
                        let a_34 := calldataload(0x46a4)
                        let var3 := mulmod(a_34, f_64, R)
                        let a_60 := calldataload(0x49e4)
                        let var4 := mulmod(a_60, f_64, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7324), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7304), sub(R, calldataload(0x72e4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7344), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7344), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_65 := calldataload(0x5644)
                        let var1 := mulmod(var0, f_65, R)
                        let a_9 := calldataload(0x4384)
                        let var2 := mulmod(a_9, f_65, R)
                        let a_35 := calldataload(0x46c4)
                        let var3 := mulmod(a_35, f_65, R)
                        let a_61 := calldataload(0x4a04)
                        let var4 := mulmod(a_61, f_65, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7384), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7364), sub(R, calldataload(0x7344)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x73a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x73a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_66 := calldataload(0x5664)
                        let var1 := mulmod(var0, f_66, R)
                        let a_10 := calldataload(0x43a4)
                        let var2 := mulmod(a_10, f_66, R)
                        let a_36 := calldataload(0x46e4)
                        let var3 := mulmod(a_36, f_66, R)
                        let a_62 := calldataload(0x4a24)
                        let var4 := mulmod(a_62, f_66, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x73e4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x73c4), sub(R, calldataload(0x73a4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7404), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7404), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_67 := calldataload(0x5684)
                        let var1 := mulmod(var0, f_67, R)
                        let a_11 := calldataload(0x43c4)
                        let var2 := mulmod(a_11, f_67, R)
                        let a_37 := calldataload(0x4704)
                        let var3 := mulmod(a_37, f_67, R)
                        let a_63 := calldataload(0x4a44)
                        let var4 := mulmod(a_63, f_67, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7444), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7424), sub(R, calldataload(0x7404)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7464), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7464), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_68 := calldataload(0x56a4)
                        let var1 := mulmod(var0, f_68, R)
                        let a_12 := calldataload(0x43e4)
                        let var2 := mulmod(a_12, f_68, R)
                        let a_38 := calldataload(0x4724)
                        let var3 := mulmod(a_38, f_68, R)
                        let a_64 := calldataload(0x4a64)
                        let var4 := mulmod(a_64, f_68, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x74a4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7484), sub(R, calldataload(0x7464)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x74c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x74c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_69 := calldataload(0x56c4)
                        let var1 := mulmod(var0, f_69, R)
                        let a_13 := calldataload(0x4404)
                        let var2 := mulmod(a_13, f_69, R)
                        let a_39 := calldataload(0x4744)
                        let var3 := mulmod(a_39, f_69, R)
                        let a_65 := calldataload(0x4a84)
                        let var4 := mulmod(a_65, f_69, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7504), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x74e4), sub(R, calldataload(0x74c4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7524), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7524), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_70 := calldataload(0x56e4)
                        let var1 := mulmod(var0, f_70, R)
                        let a_14 := calldataload(0x4424)
                        let var2 := mulmod(a_14, f_70, R)
                        let a_40 := calldataload(0x4764)
                        let var3 := mulmod(a_40, f_70, R)
                        let a_66 := calldataload(0x4aa4)
                        let var4 := mulmod(a_66, f_70, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7564), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7544), sub(R, calldataload(0x7524)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7584), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7584), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_71 := calldataload(0x5704)
                        let var1 := mulmod(var0, f_71, R)
                        let a_15 := calldataload(0x4444)
                        let var2 := mulmod(a_15, f_71, R)
                        let a_41 := calldataload(0x4784)
                        let var3 := mulmod(a_41, f_71, R)
                        let a_67 := calldataload(0x4ac4)
                        let var4 := mulmod(a_67, f_71, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x75c4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x75a4), sub(R, calldataload(0x7584)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x75e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x75e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_72 := calldataload(0x5724)
                        let var1 := mulmod(var0, f_72, R)
                        let a_16 := calldataload(0x4464)
                        let var2 := mulmod(a_16, f_72, R)
                        let a_42 := calldataload(0x47a4)
                        let var3 := mulmod(a_42, f_72, R)
                        let a_68 := calldataload(0x4ae4)
                        let var4 := mulmod(a_68, f_72, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7624), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7604), sub(R, calldataload(0x75e4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7644), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7644), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_73 := calldataload(0x5744)
                        let var1 := mulmod(var0, f_73, R)
                        let a_17 := calldataload(0x4484)
                        let var2 := mulmod(a_17, f_73, R)
                        let a_43 := calldataload(0x47c4)
                        let var3 := mulmod(a_43, f_73, R)
                        let a_69 := calldataload(0x4b04)
                        let var4 := mulmod(a_69, f_73, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7684), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7664), sub(R, calldataload(0x7644)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x76a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x76a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_74 := calldataload(0x5764)
                        let var1 := mulmod(var0, f_74, R)
                        let a_18 := calldataload(0x44a4)
                        let var2 := mulmod(a_18, f_74, R)
                        let a_44 := calldataload(0x47e4)
                        let var3 := mulmod(a_44, f_74, R)
                        let a_70 := calldataload(0x4b24)
                        let var4 := mulmod(a_70, f_74, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x76e4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x76c4), sub(R, calldataload(0x76a4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7704), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7704), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_75 := calldataload(0x5784)
                        let var1 := mulmod(var0, f_75, R)
                        let a_19 := calldataload(0x44c4)
                        let var2 := mulmod(a_19, f_75, R)
                        let a_45 := calldataload(0x4804)
                        let var3 := mulmod(a_45, f_75, R)
                        let a_71 := calldataload(0x4b44)
                        let var4 := mulmod(a_71, f_75, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7744), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7724), sub(R, calldataload(0x7704)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7764), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7764), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_76 := calldataload(0x57a4)
                        let var1 := mulmod(var0, f_76, R)
                        let a_20 := calldataload(0x44e4)
                        let var2 := mulmod(a_20, f_76, R)
                        let a_46 := calldataload(0x4824)
                        let var3 := mulmod(a_46, f_76, R)
                        let a_72 := calldataload(0x4b64)
                        let var4 := mulmod(a_72, f_76, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x77a4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7784), sub(R, calldataload(0x7764)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x77c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x77c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_77 := calldataload(0x57c4)
                        let var1 := mulmod(var0, f_77, R)
                        let a_21 := calldataload(0x4504)
                        let var2 := mulmod(a_21, f_77, R)
                        let a_47 := calldataload(0x4844)
                        let var3 := mulmod(a_47, f_77, R)
                        let a_73 := calldataload(0x4b84)
                        let var4 := mulmod(a_73, f_77, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7804), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x77e4), sub(R, calldataload(0x77c4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7824), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7824), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_78 := calldataload(0x57e4)
                        let var1 := mulmod(var0, f_78, R)
                        let a_22 := calldataload(0x4524)
                        let var2 := mulmod(a_22, f_78, R)
                        let a_48 := calldataload(0x4864)
                        let var3 := mulmod(a_48, f_78, R)
                        let a_74 := calldataload(0x4ba4)
                        let var4 := mulmod(a_74, f_78, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7864), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7844), sub(R, calldataload(0x7824)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7884), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7884), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_79 := calldataload(0x5804)
                        let var1 := mulmod(var0, f_79, R)
                        let a_23 := calldataload(0x4544)
                        let var2 := mulmod(a_23, f_79, R)
                        let a_49 := calldataload(0x4884)
                        let var3 := mulmod(a_49, f_79, R)
                        let a_75 := calldataload(0x4bc4)
                        let var4 := mulmod(a_75, f_79, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x78c4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x78a4), sub(R, calldataload(0x7884)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x78e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x78e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_80 := calldataload(0x5824)
                        let var1 := mulmod(var0, f_80, R)
                        let a_24 := calldataload(0x4564)
                        let var2 := mulmod(a_24, f_80, R)
                        let a_50 := calldataload(0x48a4)
                        let var3 := mulmod(a_50, f_80, R)
                        let a_76 := calldataload(0x4be4)
                        let var4 := mulmod(a_76, f_80, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7924), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7904), sub(R, calldataload(0x78e4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7944), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7944), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_55 := calldataload(0x5504)
                        let var1 := mulmod(var0, f_55, R)
                        let a_78 := calldataload(0x4c24)
                        let var2 := mulmod(a_78, f_55, R)
                        let a_79 := calldataload(0x4c44)
                        let var3 := mulmod(a_79, f_55, R)
                        let a_80 := calldataload(0x4c64)
                        let var4 := mulmod(a_80, f_55, R)
                        table := var1
                        table := addmod(mulmod(table, theta, R), var2, R)
                        table := addmod(mulmod(table, theta, R), var3, R)
                        table := addmod(mulmod(table, theta, R), var4, R)
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_81 := calldataload(0x5844)
                        let var1 := mulmod(var0, f_81, R)
                        let a_25 := calldataload(0x4584)
                        let var2 := mulmod(a_25, f_81, R)
                        let a_51 := calldataload(0x48c4)
                        let var3 := mulmod(a_51, f_81, R)
                        let a_77 := calldataload(0x4c04)
                        let var4 := mulmod(a_77, f_81, R)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, R), var2, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var3, R)
                        input_0 := addmod(mulmod(input_0, theta, R), var4, R)
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7984), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7964), sub(R, calldataload(0x7944)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x79a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x79a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_3 := calldataload(0x4e84)
                        let var0 := 0x1
                        let var1 := mulmod(f_3, var0, R)
                        let a_0 := calldataload(0x4264)
                        let var2 := mulmod(var1, a_0, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x79e4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x79c4), sub(R, calldataload(0x79a4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7a04), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7a04), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_4 := calldataload(0x4ea4)
                        let var0 := 0x1
                        let var1 := mulmod(f_4, var0, R)
                        let a_1 := calldataload(0x4284)
                        let var2 := mulmod(var1, a_1, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7a44), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7a24), sub(R, calldataload(0x7a04)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7a64), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7a64), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_5 := calldataload(0x4ec4)
                        let var0 := 0x1
                        let var1 := mulmod(f_5, var0, R)
                        let a_2 := calldataload(0x42a4)
                        let var2 := mulmod(var1, a_2, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7aa4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7a84), sub(R, calldataload(0x7a64)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7ac4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7ac4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_6 := calldataload(0x4ee4)
                        let var0 := 0x1
                        let var1 := mulmod(f_6, var0, R)
                        let a_3 := calldataload(0x42c4)
                        let var2 := mulmod(var1, a_3, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7b04), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7ae4), sub(R, calldataload(0x7ac4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7b24), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7b24), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_7 := calldataload(0x4f04)
                        let var0 := 0x1
                        let var1 := mulmod(f_7, var0, R)
                        let a_4 := calldataload(0x42e4)
                        let var2 := mulmod(var1, a_4, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7b64), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7b44), sub(R, calldataload(0x7b24)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7b84), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7b84), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_8 := calldataload(0x4f24)
                        let var0 := 0x1
                        let var1 := mulmod(f_8, var0, R)
                        let a_5 := calldataload(0x4304)
                        let var2 := mulmod(var1, a_5, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7bc4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7ba4), sub(R, calldataload(0x7b84)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7be4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7be4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_9 := calldataload(0x4f44)
                        let var0 := 0x1
                        let var1 := mulmod(f_9, var0, R)
                        let a_6 := calldataload(0x4324)
                        let var2 := mulmod(var1, a_6, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7c24), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7c04), sub(R, calldataload(0x7be4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7c44), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7c44), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_10 := calldataload(0x4f64)
                        let var0 := 0x1
                        let var1 := mulmod(f_10, var0, R)
                        let a_7 := calldataload(0x4344)
                        let var2 := mulmod(var1, a_7, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7c84), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7c64), sub(R, calldataload(0x7c44)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7ca4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7ca4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_11 := calldataload(0x4f84)
                        let var0 := 0x1
                        let var1 := mulmod(f_11, var0, R)
                        let a_8 := calldataload(0x4364)
                        let var2 := mulmod(var1, a_8, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7ce4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7cc4), sub(R, calldataload(0x7ca4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7d04), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7d04), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_12 := calldataload(0x4fa4)
                        let var0 := 0x1
                        let var1 := mulmod(f_12, var0, R)
                        let a_9 := calldataload(0x4384)
                        let var2 := mulmod(var1, a_9, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7d44), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7d24), sub(R, calldataload(0x7d04)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7d64), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7d64), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_13 := calldataload(0x4fc4)
                        let var0 := 0x1
                        let var1 := mulmod(f_13, var0, R)
                        let a_10 := calldataload(0x43a4)
                        let var2 := mulmod(var1, a_10, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7da4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7d84), sub(R, calldataload(0x7d64)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7dc4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7dc4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_14 := calldataload(0x4fe4)
                        let var0 := 0x1
                        let var1 := mulmod(f_14, var0, R)
                        let a_11 := calldataload(0x43c4)
                        let var2 := mulmod(var1, a_11, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7e04), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7de4), sub(R, calldataload(0x7dc4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7e24), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7e24), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_15 := calldataload(0x5004)
                        let var0 := 0x1
                        let var1 := mulmod(f_15, var0, R)
                        let a_12 := calldataload(0x43e4)
                        let var2 := mulmod(var1, a_12, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7e64), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7e44), sub(R, calldataload(0x7e24)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7e84), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7e84), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_16 := calldataload(0x5024)
                        let var0 := 0x1
                        let var1 := mulmod(f_16, var0, R)
                        let a_13 := calldataload(0x4404)
                        let var2 := mulmod(var1, a_13, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7ec4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7ea4), sub(R, calldataload(0x7e84)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7ee4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7ee4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_17 := calldataload(0x5044)
                        let var0 := 0x1
                        let var1 := mulmod(f_17, var0, R)
                        let a_14 := calldataload(0x4424)
                        let var2 := mulmod(var1, a_14, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7f24), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7f04), sub(R, calldataload(0x7ee4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7f44), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7f44), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_18 := calldataload(0x5064)
                        let var0 := 0x1
                        let var1 := mulmod(f_18, var0, R)
                        let a_15 := calldataload(0x4444)
                        let var2 := mulmod(var1, a_15, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7f84), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7f64), sub(R, calldataload(0x7f44)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x7fa4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x7fa4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_19 := calldataload(0x5084)
                        let var0 := 0x1
                        let var1 := mulmod(f_19, var0, R)
                        let a_16 := calldataload(0x4464)
                        let var2 := mulmod(var1, a_16, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x7fe4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x7fc4), sub(R, calldataload(0x7fa4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8004), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8004), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_20 := calldataload(0x50a4)
                        let var0 := 0x1
                        let var1 := mulmod(f_20, var0, R)
                        let a_17 := calldataload(0x4484)
                        let var2 := mulmod(var1, a_17, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8044), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8024), sub(R, calldataload(0x8004)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8064), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8064), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_21 := calldataload(0x50c4)
                        let var0 := 0x1
                        let var1 := mulmod(f_21, var0, R)
                        let a_18 := calldataload(0x44a4)
                        let var2 := mulmod(var1, a_18, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x80a4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8084), sub(R, calldataload(0x8064)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x80c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x80c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_22 := calldataload(0x50e4)
                        let var0 := 0x1
                        let var1 := mulmod(f_22, var0, R)
                        let a_19 := calldataload(0x44c4)
                        let var2 := mulmod(var1, a_19, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8104), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x80e4), sub(R, calldataload(0x80c4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8124), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8124), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_23 := calldataload(0x5104)
                        let var0 := 0x1
                        let var1 := mulmod(f_23, var0, R)
                        let a_20 := calldataload(0x44e4)
                        let var2 := mulmod(var1, a_20, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8164), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8144), sub(R, calldataload(0x8124)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8184), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8184), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_24 := calldataload(0x5124)
                        let var0 := 0x1
                        let var1 := mulmod(f_24, var0, R)
                        let a_21 := calldataload(0x4504)
                        let var2 := mulmod(var1, a_21, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x81c4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x81a4), sub(R, calldataload(0x8184)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x81e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x81e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_25 := calldataload(0x5144)
                        let var0 := 0x1
                        let var1 := mulmod(f_25, var0, R)
                        let a_22 := calldataload(0x4524)
                        let var2 := mulmod(var1, a_22, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8224), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8204), sub(R, calldataload(0x81e4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8244), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8244), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_26 := calldataload(0x5164)
                        let var0 := 0x1
                        let var1 := mulmod(f_26, var0, R)
                        let a_23 := calldataload(0x4544)
                        let var2 := mulmod(var1, a_23, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8284), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8264), sub(R, calldataload(0x8244)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x82a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x82a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_27 := calldataload(0x5184)
                        let var0 := 0x1
                        let var1 := mulmod(f_27, var0, R)
                        let a_24 := calldataload(0x4564)
                        let var2 := mulmod(var1, a_24, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x82e4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x82c4), sub(R, calldataload(0x82a4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8304), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8304), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_1 := calldataload(0x4e44)
                        table := f_1
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_28 := calldataload(0x51a4)
                        let var0 := 0x1
                        let var1 := mulmod(f_28, var0, R)
                        let a_25 := calldataload(0x4584)
                        let var2 := mulmod(var1, a_25, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8344), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8324), sub(R, calldataload(0x8304)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8364), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8364), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_29 := calldataload(0x51c4)
                        let var0 := 0x1
                        let var1 := mulmod(f_29, var0, R)
                        let a_0 := calldataload(0x4264)
                        let var2 := mulmod(var1, a_0, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x83a4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8384), sub(R, calldataload(0x8364)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x83c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x83c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_30 := calldataload(0x51e4)
                        let var0 := 0x1
                        let var1 := mulmod(f_30, var0, R)
                        let a_1 := calldataload(0x4284)
                        let var2 := mulmod(var1, a_1, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8404), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x83e4), sub(R, calldataload(0x83c4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8424), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8424), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_31 := calldataload(0x5204)
                        let var0 := 0x1
                        let var1 := mulmod(f_31, var0, R)
                        let a_2 := calldataload(0x42a4)
                        let var2 := mulmod(var1, a_2, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8464), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8444), sub(R, calldataload(0x8424)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8484), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8484), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_32 := calldataload(0x5224)
                        let var0 := 0x1
                        let var1 := mulmod(f_32, var0, R)
                        let a_3 := calldataload(0x42c4)
                        let var2 := mulmod(var1, a_3, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x84c4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x84a4), sub(R, calldataload(0x8484)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x84e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x84e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_33 := calldataload(0x5244)
                        let var0 := 0x1
                        let var1 := mulmod(f_33, var0, R)
                        let a_4 := calldataload(0x42e4)
                        let var2 := mulmod(var1, a_4, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8524), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8504), sub(R, calldataload(0x84e4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8544), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8544), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_34 := calldataload(0x5264)
                        let var0 := 0x1
                        let var1 := mulmod(f_34, var0, R)
                        let a_5 := calldataload(0x4304)
                        let var2 := mulmod(var1, a_5, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8584), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8564), sub(R, calldataload(0x8544)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x85a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x85a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_35 := calldataload(0x5284)
                        let var0 := 0x1
                        let var1 := mulmod(f_35, var0, R)
                        let a_6 := calldataload(0x4324)
                        let var2 := mulmod(var1, a_6, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x85e4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x85c4), sub(R, calldataload(0x85a4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8604), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8604), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_36 := calldataload(0x52a4)
                        let var0 := 0x1
                        let var1 := mulmod(f_36, var0, R)
                        let a_7 := calldataload(0x4344)
                        let var2 := mulmod(var1, a_7, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8644), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8624), sub(R, calldataload(0x8604)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8664), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8664), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_37 := calldataload(0x52c4)
                        let var0 := 0x1
                        let var1 := mulmod(f_37, var0, R)
                        let a_8 := calldataload(0x4364)
                        let var2 := mulmod(var1, a_8, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x86a4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8684), sub(R, calldataload(0x8664)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x86c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x86c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_38 := calldataload(0x52e4)
                        let var0 := 0x1
                        let var1 := mulmod(f_38, var0, R)
                        let a_9 := calldataload(0x4384)
                        let var2 := mulmod(var1, a_9, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8704), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x86e4), sub(R, calldataload(0x86c4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8724), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8724), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_39 := calldataload(0x5304)
                        let var0 := 0x1
                        let var1 := mulmod(f_39, var0, R)
                        let a_10 := calldataload(0x43a4)
                        let var2 := mulmod(var1, a_10, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8764), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8744), sub(R, calldataload(0x8724)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8784), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8784), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_40 := calldataload(0x5324)
                        let var0 := 0x1
                        let var1 := mulmod(f_40, var0, R)
                        let a_11 := calldataload(0x43c4)
                        let var2 := mulmod(var1, a_11, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x87c4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x87a4), sub(R, calldataload(0x8784)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x87e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x87e4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_41 := calldataload(0x5344)
                        let var0 := 0x1
                        let var1 := mulmod(f_41, var0, R)
                        let a_12 := calldataload(0x43e4)
                        let var2 := mulmod(var1, a_12, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8824), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8804), sub(R, calldataload(0x87e4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8844), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8844), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_42 := calldataload(0x5364)
                        let var0 := 0x1
                        let var1 := mulmod(f_42, var0, R)
                        let a_13 := calldataload(0x4404)
                        let var2 := mulmod(var1, a_13, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8884), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8864), sub(R, calldataload(0x8844)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x88a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x88a4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_43 := calldataload(0x5384)
                        let var0 := 0x1
                        let var1 := mulmod(f_43, var0, R)
                        let a_14 := calldataload(0x4424)
                        let var2 := mulmod(var1, a_14, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x88e4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x88c4), sub(R, calldataload(0x88a4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8904), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8904), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_44 := calldataload(0x53a4)
                        let var0 := 0x1
                        let var1 := mulmod(f_44, var0, R)
                        let a_15 := calldataload(0x4444)
                        let var2 := mulmod(var1, a_15, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8944), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8924), sub(R, calldataload(0x8904)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8964), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8964), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_45 := calldataload(0x53c4)
                        let var0 := 0x1
                        let var1 := mulmod(f_45, var0, R)
                        let a_16 := calldataload(0x4464)
                        let var2 := mulmod(var1, a_16, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x89a4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8984), sub(R, calldataload(0x8964)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x89c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x89c4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_46 := calldataload(0x53e4)
                        let var0 := 0x1
                        let var1 := mulmod(f_46, var0, R)
                        let a_17 := calldataload(0x4484)
                        let var2 := mulmod(var1, a_17, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8a04), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x89e4), sub(R, calldataload(0x89c4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8a24), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8a24), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_47 := calldataload(0x5404)
                        let var0 := 0x1
                        let var1 := mulmod(f_47, var0, R)
                        let a_18 := calldataload(0x44a4)
                        let var2 := mulmod(var1, a_18, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8a64), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8a44), sub(R, calldataload(0x8a24)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8a84), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8a84), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_48 := calldataload(0x5424)
                        let var0 := 0x1
                        let var1 := mulmod(f_48, var0, R)
                        let a_19 := calldataload(0x44c4)
                        let var2 := mulmod(var1, a_19, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8ac4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8aa4), sub(R, calldataload(0x8a84)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8ae4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8ae4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_49 := calldataload(0x5444)
                        let var0 := 0x1
                        let var1 := mulmod(f_49, var0, R)
                        let a_20 := calldataload(0x44e4)
                        let var2 := mulmod(var1, a_20, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8b24), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8b04), sub(R, calldataload(0x8ae4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8b44), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8b44), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_50 := calldataload(0x5464)
                        let var0 := 0x1
                        let var1 := mulmod(f_50, var0, R)
                        let a_21 := calldataload(0x4504)
                        let var2 := mulmod(var1, a_21, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8b84), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8b64), sub(R, calldataload(0x8b44)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8ba4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8ba4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_51 := calldataload(0x5484)
                        let var0 := 0x1
                        let var1 := mulmod(f_51, var0, R)
                        let a_22 := calldataload(0x4524)
                        let var2 := mulmod(var1, a_22, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8be4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8bc4), sub(R, calldataload(0x8ba4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8c04), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8c04), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_52 := calldataload(0x54a4)
                        let var0 := 0x1
                        let var1 := mulmod(f_52, var0, R)
                        let a_23 := calldataload(0x4544)
                        let var2 := mulmod(var1, a_23, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8c44), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8c24), sub(R, calldataload(0x8c04)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8c64), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8c64), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_53 := calldataload(0x54c4)
                        let var0 := 0x1
                        let var1 := mulmod(f_53, var0, R)
                        let a_24 := calldataload(0x4564)
                        let var2 := mulmod(var1, a_24, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8ca4), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8c84), sub(R, calldataload(0x8c64)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x8cc4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x8cc4), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x4e64)
                        table := f_2
                        table := addmod(table, beta, R)
                    }
                    let input_0
                    {
                        let f_54 := calldataload(0x54e4)
                        let var0 := 0x1
                        let var1 := mulmod(f_54, var0, R)
                        let a_25 := calldataload(0x4584)
                        let var2 := mulmod(var1, a_25, R)
                        let var3 := sub(R, var1)
                        let var4 := addmod(var0, var3, R)
                        let var5 := 0x0
                        let var6 := mulmod(var4, var5, R)
                        let var7 := addmod(var2, var6, R)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, R)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(R, mulmod(calldataload(0x8d04), tmp, R)), R)
                        lhs := mulmod(mulmod(table, tmp, R), addmod(calldataload(0x8ce4), sub(R, calldataload(0x8cc4)), R), R)
                    }
                    let eval := mulmod(addmod(1, sub(R, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), R)), R), addmod(lhs, sub(R, rhs), R), R)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }

                pop(y)

                let quotient_eval := mulmod(quotient_eval_numer, mload(X_N_MINUS_1_INV_MPTR), r)
                mstore(QUOTIENT_EVAL_MPTR, quotient_eval)
            }

            // Compute quotient commitment
            {
                mstore(0x00, calldataload(LAST_QUOTIENT_X_CPTR))
                mstore(0x20, calldataload(add(LAST_QUOTIENT_X_CPTR, 0x20)))
                let x_n := mload(X_N_MPTR)
                for
                    {
                        let cptr := sub(LAST_QUOTIENT_X_CPTR, 0x40)
                        let cptr_end := sub(FIRST_QUOTIENT_X_CPTR, 0x40)
                    }
                    lt(cptr_end, cptr)
                    {}
                {
                    success := ec_mul_acc(success, x_n)
                    success := ec_add_acc(success, calldataload(cptr), calldataload(add(cptr, 0x20)))
                    cptr := sub(cptr, 0x40)
                }
                mstore(QUOTIENT_X_MPTR, mload(0x00))
                mstore(QUOTIENT_Y_MPTR, mload(0x20))
            }

            // Compute pairing lhs and rhs
            {
                {
                    let x := mload(X_MPTR)
                    let omega := mload(OMEGA_MPTR)
                    let omega_inv := mload(OMEGA_INV_MPTR)
                    let x_pow_of_omega := mulmod(x, omega, R)
                    mstore(0x0360, x_pow_of_omega)
                    mstore(0x0340, x)
                    x_pow_of_omega := mulmod(x, omega_inv, R)
                    mstore(0x0320, x_pow_of_omega)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, R)
                    mstore(0x0300, x_pow_of_omega)
                }
                {
                    let mu := mload(MU_MPTR)
                    for
                        {
                            let mptr := 0x0380
                            let mptr_end := 0x0400
                            let point_mptr := 0x0300
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            point_mptr := add(point_mptr, 0x20)
                        }
                    {
                        mstore(mptr, addmod(mu, sub(R, mload(point_mptr)), R))
                    }
                    let s
                    s := mload(0x03c0)
                    mstore(0x0400, s)
                    let diff
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), R)
                    diff := mulmod(diff, mload(0x03e0), R)
                    mstore(0x0420, diff)
                    mstore(0x00, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03e0), R)
                    mstore(0x0440, diff)
                    diff := mload(0x03a0)
                    mstore(0x0460, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), R)
                    mstore(0x0480, diff)
                }
                {
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := 1
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0x20, coeff)
                }
                {
                    let point_1 := mload(0x0320)
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := addmod(point_1, sub(R, point_2), R)
                    coeff := mulmod(coeff, mload(0x03a0), R)
                    mstore(0x40, coeff)
                    coeff := addmod(point_2, sub(R, point_1), R)
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0x60, coeff)
                }
                {
                    let point_0 := mload(0x0300)
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_0, sub(R, point_2), R)
                    coeff := mulmod(coeff, addmod(point_0, sub(R, point_3), R), R)
                    coeff := mulmod(coeff, mload(0x0380), R)
                    mstore(0x80, coeff)
                    coeff := addmod(point_2, sub(R, point_0), R)
                    coeff := mulmod(coeff, addmod(point_2, sub(R, point_3), R), R)
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0xa0, coeff)
                    coeff := addmod(point_3, sub(R, point_0), R)
                    coeff := mulmod(coeff, addmod(point_3, sub(R, point_2), R), R)
                    coeff := mulmod(coeff, mload(0x03e0), R)
                    mstore(0xc0, coeff)
                }
                {
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_2, sub(R, point_3), R)
                    coeff := mulmod(coeff, mload(0x03c0), R)
                    mstore(0xe0, coeff)
                    coeff := addmod(point_3, sub(R, point_2), R)
                    coeff := mulmod(coeff, mload(0x03e0), R)
                    mstore(0x0100, coeff)
                }
                {
                    success := batch_invert(success, 0, 0x0120)
                    let diff_0_inv := mload(0x00)
                    mstore(0x0420, diff_0_inv)
                    for
                        {
                            let mptr := 0x0440
                            let mptr_end := 0x04a0
                        }
                        lt(mptr, mptr_end)
                        { mptr := add(mptr, 0x20) }
                    {
                        mstore(mptr, mulmod(mload(mptr), diff_0_inv, R))
                    }
                }
                {
                    let coeff := mload(0x20)
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x5da4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, mload(QUOTIENT_EVAL_MPTR), R), R)
                    for
                        {
                            let mptr := 0x6804
                            let mptr_end := 0x5da4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, R), mulmod(coeff, calldataload(mptr), R), R)
                    }
                    for
                        {
                            let mptr := 0x5d84
                            let mptr_end := 0x4e04
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, R), mulmod(coeff, calldataload(mptr), R), R)
                    }
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8d04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8ca4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8c44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8be4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8b84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8b24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8ac4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8a64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8a04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x89a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8944), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x88e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8884), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8824), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x87c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8764), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8704), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x86a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8644), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x85e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8584), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8524), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x84c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8464), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8404), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x83a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8344), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x82e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8284), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8224), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x81c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8164), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8104), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x80a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x8044), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7fe4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7f84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7f24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7ec4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7e64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7e04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7da4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7d44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7ce4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7c84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7c24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7bc4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7b64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7b04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7aa4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7a44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x79e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7984), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7924), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x78c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7864), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7804), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x77a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7744), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x76e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7684), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7624), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x75c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7564), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7504), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x74a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7444), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x73e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7384), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7324), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x72c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7264), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7204), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x71a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7144), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x70e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7084), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x7024), R), R)
                    for
                        {
                            let mptr := 0x4c64
                            let mptr_end := 0x4be4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, R), mulmod(coeff, calldataload(mptr), R), R)
                    }
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4bc4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4b84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4b44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4b04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4ac4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4a84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4a44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4a04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x49c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4984), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4944), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x4904), R), R)
                    for
                        {
                            let mptr := 0x48c4
                            let mptr_end := 0x4244
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, R), mulmod(coeff, calldataload(mptr), R), R)
                    }
                    mstore(0x04a0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4e04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4be4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4de4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4ba4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4dc4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4b64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4da4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4b24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4d84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4ae4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4d64), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4aa4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4d44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4a64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4d24), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4a24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4d04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x49e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4ce4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x49a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4cc4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4964), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4ca4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x4924), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x4c84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x48e4), R), R)
                    r_eval := mulmod(r_eval, mload(0x0440), R)
                    mstore(0x04c0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6f84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6f44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6f64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6f24), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6ee4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6f04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6ec4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6e84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6ea4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6e64), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6e24), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6e44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6e04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6dc4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6de4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6da4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6d64), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6d84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6d44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6d04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6d24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6ce4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6ca4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6cc4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6c84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6c44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6c64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6c24), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6be4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6c04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6bc4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6b84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6ba4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6b64), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6b24), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6b44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6b04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6ac4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6ae4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6aa4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6a64), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6a84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6a44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6a04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6a24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x69e4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x69a4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x69c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6984), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6944), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6964), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6924), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x68e4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6904), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x68c4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6884), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x68a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x6864), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x6824), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x6844), R), R)
                    r_eval := mulmod(r_eval, mload(0x0460), R)
                    mstore(0x04e0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8cc4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8ce4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8c64), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8c84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8c04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8c24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8ba4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8bc4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8b44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8b64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8ae4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8b04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8a84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8aa4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8a24), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8a44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x89c4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x89e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8964), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8984), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8904), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8924), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x88a4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x88c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8844), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8864), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x87e4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8804), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8784), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x87a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8724), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8744), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x86c4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x86e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8664), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8684), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8604), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8624), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x85a4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x85c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8544), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8564), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x84e4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8504), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8484), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x84a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8424), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8444), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x83c4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x83e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8364), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8384), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8304), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8324), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x82a4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x82c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8244), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8264), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x81e4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8204), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8184), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x81a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8124), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8144), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x80c4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x80e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8064), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8084), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x8004), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x8024), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7fa4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7fc4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7f44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7f64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7ee4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7f04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7e84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7ea4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7e24), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7e44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7dc4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7de4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7d64), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7d84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7d04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7d24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7ca4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7cc4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7c44), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7c64), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7be4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7c04), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7b84), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7ba4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7b24), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7b44), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7ac4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7ae4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7a64), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7a84), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7a04), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7a24), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x79a4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x79c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7944), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7964), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x78e4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7904), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7884), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x78a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7824), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7844), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x77c4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x77e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7764), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7784), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7704), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7724), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x76a4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x76c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7644), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7664), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x75e4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7604), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7584), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x75a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7524), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7544), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x74c4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x74e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7464), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7484), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7404), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7424), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x73a4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x73c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7344), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7364), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x72e4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7304), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7284), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x72a4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7224), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7244), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x71c4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x71e4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7164), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7184), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7104), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7124), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x70a4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x70c4), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x7044), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7064), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x6fe4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x7004), R), R)
                    r_eval := mulmod(r_eval, zeta, R)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x6fa4), R), R)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x6fc4), R), R)
                    r_eval := mulmod(r_eval, mload(0x0480), R)
                    mstore(0x0500, r_eval)
                }
                {
                    let sum := mload(0x20)
                    mstore(0x0520, sum)
                }
                {
                    let sum := mload(0x40)
                    sum := addmod(sum, mload(0x60), R)
                    mstore(0x0540, sum)
                }
                {
                    let sum := mload(0x80)
                    sum := addmod(sum, mload(0xa0), R)
                    sum := addmod(sum, mload(0xc0), R)
                    mstore(0x0560, sum)
                }
                {
                    let sum := mload(0xe0)
                    sum := addmod(sum, mload(0x0100), R)
                    mstore(0x0580, sum)
                }
                {
                    for
                        {
                            let mptr := 0x00
                            let mptr_end := 0x80
                            let sum_mptr := 0x0520
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            sum_mptr := add(sum_mptr, 0x20)
                        }
                    {
                        mstore(mptr, mload(sum_mptr))
                    }
                    success := batch_invert(success, 0, 0x80)
                    let r_eval := mulmod(mload(0x60), mload(0x0500), R)
                    for
                        {
                            let sum_inv_mptr := 0x40
                            let sum_inv_mptr_end := 0x80
                            let r_eval_mptr := 0x04e0
                        }
                        lt(sum_inv_mptr, sum_inv_mptr_end)
                        {
                            sum_inv_mptr := sub(sum_inv_mptr, 0x20)
                            r_eval_mptr := sub(r_eval_mptr, 0x20)
                        }
                    {
                        r_eval := mulmod(r_eval, mload(NU_MPTR), R)
                        r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), R), R)
                    }
                    mstore(R_EVAL_MPTR, r_eval)
                }
                {
                    let nu := mload(NU_MPTR)
                    mstore(0x00, calldataload(0x40e4))
                    mstore(0x20, calldataload(0x4104))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, mload(QUOTIENT_X_MPTR), mload(QUOTIENT_Y_MPTR))
                    for
                        {
                            let mptr := 0x4aa0
                            let mptr_end := 0x16e0
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, mload(mptr), mload(add(mptr, 0x20)))
                    }
                    for
                        {
                            let mptr := 0x27e4
                            let mptr_end := 0x1364
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x1324), calldataload(0x1344))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x12a4), calldataload(0x12c4))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x1224), calldataload(0x1244))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x11a4), calldataload(0x11c4))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x1124), calldataload(0x1144))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x10a4), calldataload(0x10c4))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x1024), calldataload(0x1044))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x0fa4), calldataload(0x0fc4))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x0f24), calldataload(0x0f44))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x0ea4), calldataload(0x0ec4))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x0e24), calldataload(0x0e44))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, calldataload(0x0da4), calldataload(0x0dc4))
                    for
                        {
                            let mptr := 0x0d24
                            let mptr_end := 0x24
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    mstore(0x80, calldataload(0x1364))
                    mstore(0xa0, calldataload(0x1384))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x12e4), calldataload(0x1304))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x1264), calldataload(0x1284))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x11e4), calldataload(0x1204))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x1164), calldataload(0x1184))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x10e4), calldataload(0x1104))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x1064), calldataload(0x1084))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x0fe4), calldataload(0x1004))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x0f64), calldataload(0x0f84))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x0ee4), calldataload(0x0f04))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x0e64), calldataload(0x0e84))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x0de4), calldataload(0x0e04))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x0d64), calldataload(0x0d84))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0440), R))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), R)
                    mstore(0x80, calldataload(0x2ce4))
                    mstore(0xa0, calldataload(0x2d04))
                    for
                        {
                            let mptr := 0x2ca4
                            let mptr_end := 0x27e4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, mload(ZETA_MPTR))
                        success := ec_add_tmp(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0460), R))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), R)
                    mstore(0x80, calldataload(0x40a4))
                    mstore(0xa0, calldataload(0x40c4))
                    for
                        {
                            let mptr := 0x4064
                            let mptr_end := 0x2ce4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, mload(ZETA_MPTR))
                        success := ec_add_tmp(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0480), R))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, mload(G1_X_MPTR))
                    mstore(0xa0, mload(G1_Y_MPTR))
                    success := ec_mul_tmp(success, sub(R, mload(R_EVAL_MPTR)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x8d24))
                    mstore(0xa0, calldataload(0x8d44))
                    success := ec_mul_tmp(success, sub(R, mload(0x0400)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x8d64))
                    mstore(0xa0, calldataload(0x8d84))
                    success := ec_mul_tmp(success, mload(MU_MPTR))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                    mstore(PAIRING_LHS_Y_MPTR, mload(0x20))
                    mstore(PAIRING_RHS_X_MPTR, calldataload(0x8d64))
                    mstore(PAIRING_RHS_Y_MPTR, calldataload(0x8d84))
                }
            }

            // Random linear combine with accumulator
            if mload(HAS_ACCUMULATOR_MPTR) {
                mstore(0x00, mload(ACC_LHS_X_MPTR))
                mstore(0x20, mload(ACC_LHS_Y_MPTR))
                mstore(0x40, mload(ACC_RHS_X_MPTR))
                mstore(0x60, mload(ACC_RHS_Y_MPTR))
                mstore(0x80, mload(PAIRING_LHS_X_MPTR))
                mstore(0xa0, mload(PAIRING_LHS_Y_MPTR))
                mstore(0xc0, mload(PAIRING_RHS_X_MPTR))
                mstore(0xe0, mload(PAIRING_RHS_Y_MPTR))
                let challenge := mod(keccak256(0x00, 0x100), r)

                // [pairing_lhs] += challenge * [acc_lhs]
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_LHS_X_MPTR), mload(PAIRING_LHS_Y_MPTR))
                mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                mstore(PAIRING_LHS_Y_MPTR, mload(0x20))

                // [pairing_rhs] += challenge * [acc_rhs]
                mstore(0x00, mload(ACC_RHS_X_MPTR))
                mstore(0x20, mload(ACC_RHS_Y_MPTR))
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_RHS_X_MPTR), mload(PAIRING_RHS_Y_MPTR))
                mstore(PAIRING_RHS_X_MPTR, mload(0x00))
                mstore(PAIRING_RHS_Y_MPTR, mload(0x20))
            }

            // Perform pairing
            success := ec_pairing(
                success,
                mload(PAIRING_LHS_X_MPTR),
                mload(PAIRING_LHS_Y_MPTR),
                mload(PAIRING_RHS_X_MPTR),
                mload(PAIRING_RHS_Y_MPTR)
            )

            // Revert if anything fails
            if iszero(success) {
                revert(0x00, 0x00)
            }

            // Return 1 as result if everything succeeds
            mstore(0x00, 1)
            return(0x00, 0x20)
        }
    }
}