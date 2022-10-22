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

    func sqrt{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}(x: Uint256) -> (res: Uint256) {
        alloc_locals;

        let borders: Uint256* = alloc();
        assert borders[0] = Uint256(low=0, high=1);
        assert borders[1] = Uint256(low=18446744073709551616, high=0);
        assert borders[2] = Uint256(low=4294967296, high=0);
        assert borders[3] = Uint256(low=65536, high=0);
        assert borders[4] = Uint256(low=256, high=0);
        assert borders[5] = Uint256(low=16, high=0);
        assert borders[6] = Uint256(low=8, high=0);

        let shiftingValues: felt* = alloc();
        assert shiftingValues[0] = 128;
        assert shiftingValues[1] = 64;
        assert shiftingValues[2] = 64;
        assert shiftingValues[3] = 32;
        assert shiftingValues[4] = 32;
        assert shiftingValues[5] = 16;
        assert shiftingValues[6] = 16;
        assert shiftingValues[7] = 8;
        assert shiftingValues[8] = 8;
        assert shiftingValues[9] = 4;
        assert shiftingValues[10] = 4;
        assert shiftingValues[11] = 2;
        assert shiftingValues[12] = 0;
        assert shiftingValues[13] = 1;

        let (temp_y, temp_z) = _assignYAndZForSQRT(
            borders_len=7,
            borders=borders,
            y=x, 
            z=Uint256(low=1, high=0),
            shiftingValues_len=14,
            shiftingValues=shiftingValues
        );

        let (z) = _shiftZ(7, x, temp_z);
        let (zRoundDown, zRoundDownRem) = uint256_unsigned_div_rem(x, z);

        let (zRoundDownLower) = uint256_lt(zRoundDown, z);
        if(zRoundDownLower == TRUE) {
            return (res=zRoundDown);
        }

        return (res=z);
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

    func _assignYAndZForSQRT{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}(
        borders_len: felt,
        borders: Uint256*,
        y: Uint256, 
        z: Uint256,
        shiftingValues_len: felt,
        shiftingValues: felt*
    ) -> (y: Uint256, z: Uint256) {
        alloc_locals;

        if(borders_len == 0) {
            return (y=y, z=z);
        } 
    
        // Uint256(low=0, high=1) = 0x100000000000000000000000000000000
        let (LT) = uint256_lt(y, [borders]);
        if(LT == FALSE) {
            let (temp_y) = uint256_shr(y, Uint256(low=[shiftingValues], high=0));
            let (temp_z) = uint256_shl(z, Uint256(low=[shiftingValues + 1], high=0));

            return _assignYAndZForSQRT(
                borders_len - 1,
                borders + 1,
                temp_y,
                temp_z,
                shiftingValues_len,
                shiftingValues + 2
            );
        } 

        return _assignYAndZForSQRT(
            borders_len - 1,
            borders + 1,
            y,
            z,
            shiftingValues_len,
            shiftingValues + 2
        );
    }

    func _shiftZ{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}(
        iterationAmount: felt,
        x: Uint256,
        z: Uint256
    ) -> (res: Uint256) {

        if(iterationAmount == 0) {
            return (res=z);
        }

        let (division, divRem) = uint256_unsigned_div_rem(x, z);
        let (addition, additionCarry) = uint256_add(z, division);
        let (temp_z, temp_z_rem) = uint256_unsigned_div_rem(addition, Uint256(low=2, high=0));

        return _shiftZ(iterationAmount - 1, x, temp_z);
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