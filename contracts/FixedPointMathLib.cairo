%lang starknet

from starkware.cairo.common.alloc import (alloc)
from starkware.cairo.common.cairo_builtins import (HashBuiltin)
from starkware.cairo.common.bool import (TRUE, FALSE)
from starkware.cairo.common.uint256 import (
    Uint256,
    uint256_add,
    uint256_mul,
    uint256_le,
    uint256_lt,
    uint256_eq,
    uint256_shr,
    uint256_shl,
    uint256_unsigned_div_rem
)

namespace FixedPointMathLib {
    func fmul{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}(
        x: Uint256,
        y: Uint256,
        baseUnit: Uint256
    ) -> (res: Uint256) {
        alloc_locals;
        let (_z, _zHigh) = uint256_mul(x, y);

        // assert (x == 0 || ((x * y) / x) == y)
        let (xIsZero) = uint256_eq(x, Uint256(low=0, high=0));
        if (xIsZero == FALSE) {
            let (shouldBeY, _r) = uint256_unsigned_div_rem(_z, x);
            assert shouldBeY.low = y.low;
            assert shouldBeY.high = y.high;

            tempvar syscall_ptr = syscall_ptr;
            tempvar pedersen_ptr = pedersen_ptr;
            tempvar range_check_ptr = range_check_ptr;
        } else {
            tempvar syscall_ptr = syscall_ptr;
            tempvar pedersen_ptr = pedersen_ptr;
            tempvar range_check_ptr = range_check_ptr;
        }

        tempvar syscall_ptr = syscall_ptr;
        tempvar pedersen_ptr = pedersen_ptr;
        tempvar range_check_ptr = range_check_ptr;

        let (z, r) = uint256_unsigned_div_rem(_z, baseUnit);

        return (res=z);
    }

    func fdiv{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}(
        x: Uint256,
        y: Uint256,
        baseUnit: Uint256
    ) -> (res: Uint256) {
        alloc_locals;
        let (_z, _zHigh) = uint256_mul(x, baseUnit);

        // assert y !== 0
        let (yIsZero) = uint256_eq(y, Uint256(low=0, high=0));
        assert yIsZero = FALSE;

        // assert x == 0 || ((x * baseUnit) / x) == baseUnit
        let (xIsZero) = uint256_eq(x, Uint256(low=0, high=0));
        if (xIsZero == FALSE) {
            let (shouldBeBaseUnit, _r) = uint256_unsigned_div_rem(_z, x);
            assert shouldBeBaseUnit.low = baseUnit.low;
            assert shouldBeBaseUnit.high = baseUnit.high;

            tempvar syscall_ptr = syscall_ptr;
            tempvar pedersen_ptr = pedersen_ptr;
            tempvar range_check_ptr = range_check_ptr;
        } else {
            tempvar syscall_ptr = syscall_ptr;
            tempvar pedersen_ptr = pedersen_ptr;
            tempvar range_check_ptr = range_check_ptr;
        }

        tempvar syscall_ptr = syscall_ptr;
        tempvar pedersen_ptr = pedersen_ptr;
        tempvar range_check_ptr = range_check_ptr;

        let (z, r) = uint256_unsigned_div_rem(_z, y);

        return (res=z);

    }

    func fpow{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}(
        x: Uint256,
        n: Uint256,
        baseUnit: Uint256
    ) -> (res: Uint256) {
        alloc_locals;

        let (xIsZero) = uint256_eq(x, Uint256(low=0, high=0));

        if(xIsZero == TRUE) {
            let (nIsZero) = uint256_eq(n, Uint256(low=0, high=0));
            if(nIsZero == TRUE) {
                // 0**0 = 1               
                return (res=Uint256(low=1, high=0));
            } 
            // 0**n = 0
            return (res=Uint256(low=0, high=0));
        }

        let (nHalf, nHalfRem) = uint256_unsigned_div_rem(n, Uint256(low=2, high=0));
        let (nIsEven) = uint256_eq(nHalfRem, Uint256(low=0, high=0));
        let (z) = FixedPointMathLib._assignZIf(nIsEven, baseUnit, x);

        let (baseUnitHalf, baseUnitHalfRem) = uint256_unsigned_div_rem(baseUnit, Uint256(low=2, high=0));

        // Simulate the for loop but with recursion
        let (res) = fpow_loop(x, nHalf, z, baseUnit, baseUnitHalf);

        return (res=res);
    }

    // Loop should start with n / 2, stop with n <= 0 and iterate with n = n / 2
    func fpow_loop{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}(
        x: Uint256, 
        n: Uint256, 
        z: Uint256,
        baseUnit: Uint256,
        baseUnitHalf: Uint256
    ) -> (res: Uint256) {
        alloc_locals;

        // end of the loop of n <= 0
        let (n_LteZero) = uint256_le(n, Uint256(low=0, high=0));
        if(n_LteZero == TRUE) {
            return (res=z);
        }

        // store x squared
        let (xx, xxOverflow) = uint256_mul(x, x);
        assert xxOverflow.low = 0;
        assert xxOverflow.high = 0;

        // Round to the nearest number
        let (xxRound, xSquaredRoundCarry) = uint256_add(xx, baseUnitHalf);
        let (roundingOverflowed) = uint256_lt(xxRound, xx);
        assert roundingOverflowed = FALSE;

        // Set x to scaled xxRound
        let (temp_x, temp_x_rem) = uint256_unsigned_div_rem(xxRound, baseUnit);

        // Immediately continue the loop if n is even
        let (nHalf, nHalfRem) = uint256_unsigned_div_rem(n, Uint256(low=2, high=0));
        let (nHalfIsEven) = uint256_eq(nHalfRem, Uint256(low=0, high=0));
        if(nHalfIsEven == TRUE) {
            // continue looping with n = n / 2
            return fpow_loop(x=temp_x, n=nHalf, z=z, baseUnit=baseUnit, baseUnitHalf=baseUnitHalf);
        }

        // Compute z * x
        let (zx, zxOverflow) = uint256_mul(z, temp_x);
        assert zxOverflow.low = 0;
        assert zxOverflow.high = 0;

        // Revert of overflow
        let (shouldBeZ, shouldBeZRem) = uint256_unsigned_div_rem(zx, temp_x);
        let (zxNotOverflowed) = uint256_eq(shouldBeZ, z);
        assert zxNotOverflowed = TRUE;

        // Round to the nearest number
        let (zxRound, zxRoundCarry) = uint256_add(zx, baseUnitHalf);
        let (zxRoundOverflowed) = uint256_lt(zxRound, zx);
        assert zxRoundOverflowed = FALSE;

        // Continue loop with the properly scaled zxRound
        let (temp_z, temp_zRem) = uint256_unsigned_div_rem(zxRound, baseUnit);

        return fpow_loop(x=temp_x, n=nHalf, z=temp_z, baseUnit=baseUnit, baseUnitHalf=baseUnitHalf);
    }

    func _assignZIf{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}(
        nIsEven: felt,
        baseUnit: Uint256,
        x: Uint256
    ) -> (res: Uint256) {
        if(nIsEven == TRUE) {
            // If n is even, store baseUnit in z for now
            return (res=baseUnit);
        }
        // Else store x in z for now
        return (res=x);
    }

    func YAD{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}() -> (res: Uint256) {
        // 1e8
        let YAD = Uint256(low=10**8, high=0);
        return (res=YAD);
    }

    func WAD{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}() -> (res: Uint256) {
        // 1e18
        let WAD = Uint256(low=10**18, high=0);
        return (res=WAD);
    }

    func RAY{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}() -> (res: Uint256) {
        // 1e27
        let RAY = Uint256(low=10**27, high=0);
        return (res=RAY);
    }

    func RAD{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}() -> (res: Uint256) {
        // 1e45
        let RAD = Uint256(low=298446595834331248847564553865037611008, high=2938735);
        return (res=RAD);
    }
}


//////////////////////////////
// Original Solidity Contract

// // SPDX-License-Identifier: AGPL-3.0-only
// pragma solidity >=0.8.0;

// /// @notice Arithmetic library with operations for fixed-point numbers.
// /// @author Solmate (https://github.com/Rari-Capital/solmate/blob/main/src/utils/FixedPointMathLib.sol)
// library FixedPointMathLib {
//     /*///////////////////////////////////////////////////////////////
//                             COMMON BASE UNITS
//     //////////////////////////////////////////////////////////////*/

//     uint256 internal constant YAD = 1e8;
//     uint256 internal constant WAD = 1e18;
//     uint256 internal constant RAY = 1e27;
//     uint256 internal constant RAD = 1e45;

//     /*///////////////////////////////////////////////////////////////
//                          FIXED POINT OPERATIONS
//     //////////////////////////////////////////////////////////////*/

//     function fmul(
//         uint256 x,
//         uint256 y,
//         uint256 baseUnit
//     ) internal pure returns (uint256 z) {
//         assembly {
//             // Store x * y in z for now.
//             z := mul(x, y)

//             // Equivalent to require(x == 0 || (x * y) / x == y)
//             if iszero(or(iszero(x), eq(div(z, x), y))) {
//                 revert(0, 0)
//             }

//             // If baseUnit is zero this will return zero instead of reverting.
//             z := div(z, baseUnit)
//         }
//     }

//     function fdiv(
//         uint256 x,
//         uint256 y,
//         uint256 baseUnit
//     ) internal pure returns (uint256 z) {
//         assembly {
//             // Store x * baseUnit in z for now.
//             z := mul(x, baseUnit)

//             // Equivalent to require(y != 0 && (x == 0 || (x * baseUnit) / x == baseUnit))
//             if iszero(and(iszero(iszero(y)), or(iszero(x), eq(div(z, x), baseUnit)))) {
//                 revert(0, 0)
//             }

//             // We ensure y is not zero above, so there is never division by zero here.
//             z := div(z, y)
//         }
//     }

//     function fpow(
//         uint256 x,
//         uint256 n,
//         uint256 baseUnit
//     ) internal pure returns (uint256 z) {
//         assembly {
//             switch x
//             case 0 {
//                 switch n
//                 case 0 {
//                     // 0 ** 0 = 1
//                     z := baseUnit
//                 }
//                 default {
//                     // 0 ** n = 0
//                     z := 0
//                 }
//             }
//             default {
//                 switch mod(n, 2)
//                 case 0 {
//                     // If n is even, store baseUnit in z for now.
//                     z := baseUnit
//                 }
//                 default {
//                     // If n is odd, store x in z for now.
//                     z := x
//                 }

//                 // Shifting right by 1 is like dividing by 2.
//                 let half := shr(1, baseUnit)

//                 for {
//                     // Shift n right by 1 before looping to halve it.
//                     n := shr(1, n)
//                 } n {
//                     // Shift n right by 1 each iteration to halve it.
//                     n := shr(1, n)
//                 } {
//                     // Revert immediately if x ** 2 would overflow.
//                     // Equivalent to iszero(eq(div(xx, x), x)) here.
//                     if shr(128, x) {
//                         revert(0, 0)
//                     }

//                     // Store x squared.
//                     let xx := mul(x, x)

//                     // Round to the nearest number.
//                     let xxRound := add(xx, half)

//                     // Revert if xx + half overflowed.
//                     if lt(xxRound, xx) {
//                         revert(0, 0)
//                     }

//                     // Set x to scaled xxRound.
//                     x := div(xxRound, baseUnit)

//                     // If n is not even:
//                     if mod(n, 2) {
//                         // Compute z * x.
//                         let zx := mul(z, x)

//                         // If z * x overflowed:
//                         if iszero(eq(div(zx, x), z)) {
//                             // Revert if x is non-zero.
//                             if iszero(iszero(x)) {
//                                 revert(0, 0)
//                             }
//                         }

//                         // Round to the nearest number.
//                         let zxRound := add(zx, half)

//                         // Revert if zx + half overflowed.
//                         if lt(zxRound, zx) {
//                             revert(0, 0)
//                         }

//                         // Return properly scaled zxRound.
//                         z := div(zxRound, baseUnit)
//                     }
//                 }
//             }
//         }
//     }

//     /*///////////////////////////////////////////////////////////////
//                         GENERAL NUMBER UTILITIES
//     //////////////////////////////////////////////////////////////*/

//     function sqrt(uint256 x) internal pure returns (uint256 z) {
//         assembly {
//             // Start off with z at 1.
//             z := 1

//             // Used below to help find a nearby power of 2.
//             let y := x

//             // Find the lowest power of 2 that is at least sqrt(x).
//             if iszero(lt(y, 0x100000000000000000000000000000000)) {
//                 y := shr(128, y) // Like dividing by 2 ** 128.
//                 z := shl(64, z)
//             }
//             if iszero(lt(y, 0x10000000000000000)) {
//                 y := shr(64, y) // Like dividing by 2 ** 64.
//                 z := shl(32, z)
//             }
//             if iszero(lt(y, 0x100000000)) {
//                 y := shr(32, y) // Like dividing by 2 ** 32.
//                 z := shl(16, z)
//             }
//             if iszero(lt(y, 0x10000)) {
//                 y := shr(16, y) // Like dividing by 2 ** 16.
//                 z := shl(8, z)
//             }
//             if iszero(lt(y, 0x100)) {
//                 y := shr(8, y) // Like dividing by 2 ** 8.
//                 z := shl(4, z)
//             }
//             if iszero(lt(y, 0x10)) {
//                 y := shr(4, y) // Like dividing by 2 ** 4.
//                 z := shl(2, z)
//             }
//             if iszero(lt(y, 0x8)) {
//                 // Equivalent to 2 ** z.
//                 z := shl(1, z)
//             }

//             // Shifting right by 1 is like dividing by 2.
//             z := shr(1, add(z, div(x, z)))
//             z := shr(1, add(z, div(x, z)))
//             z := shr(1, add(z, div(x, z)))
//             z := shr(1, add(z, div(x, z)))
//             z := shr(1, add(z, div(x, z)))
//             z := shr(1, add(z, div(x, z)))
//             z := shr(1, add(z, div(x, z)))

//             // Compute a rounded down version of z.
//             let zRoundDown := div(x, z)

//             // If zRoundDown is smaller, use it.
//             if lt(zRoundDown, z) {
//                 z := zRoundDown
//             }
//         }
//     }
// }