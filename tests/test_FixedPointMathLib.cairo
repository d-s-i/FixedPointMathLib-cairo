%lang starknet

from starkware.cairo.common.alloc import (alloc)

from starkware.cairo.common.cairo_builtins import (HashBuiltin)
from starkware.cairo.common.uint256 import (
    Uint256, 
    uint256_lt,
    uint256_le,
    uint256_eq,
    uint256_unsigned_div_rem,
    uint256_add,
    uint256_mul,
    uint256_sqrt
)
from starkware.cairo.common.bool import (TRUE, FALSE)

from contracts.FixedPointMathLib import (FixedPointMathLib)

@external
func test_WAD{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr}() {
    let (shouldBeWAD) = FixedPointMathLib.WAD();

    %{ print("WAD: ", int(ids.shouldBeWAD.low) + int(ids.shouldBeWAD.high)) %}

    const WAD_VALUE = 10**18;
    assert shouldBeWAD.low = WAD_VALUE;

    return ();
}

@external
func test_fmul{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}() {
    alloc_locals;

    local x: Uint256 = Uint256(low=10000000000000000000, high=0);
    local y: Uint256 = Uint256(low=150000000000000000000, high=0);
    local expectedResult: Uint256 = Uint256(low=1500000000000000000000, high=0);

    %{ 
        x = reflect.x.get()
        y = reflect.y.get()
    %}

    let (WAD) = FixedPointMathLib.WAD();
    let (res) = FixedPointMathLib.fmul(x, y, WAD);

    %{ 
        print(f"x {x.low}")
        print(f"y {y.low}")
        print(f"res {ids.res.low}")
    %}

    let (isCorrect) = uint256_eq(res, expectedResult);
    assert isCorrect = TRUE;

    return ();
}

@external
func test_fdiv{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}() {
    alloc_locals;

    local x: Uint256 = Uint256(low=10000000000000000000, high=0);
    local y: Uint256 = Uint256(low=150000000000000000000, high=0);
    local expectedResult: Uint256 = Uint256(low=66666666666666666, high=0);

    %{ 
        x = reflect.x.get()
        y = reflect.y.get()
    %}

    let (WAD) = FixedPointMathLib.WAD();
    let (res) = FixedPointMathLib.fdiv(x, y, WAD);

    %{ 
        print(f"x {x.low}")
        print(f"y {y.low}")
        print(f"res {ids.res.low}")
    %}

    let (isCorrect) = uint256_eq(res, expectedResult);
    assert isCorrect = TRUE;

    return ();
}

@external
func test_fpow_1{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}() {
    alloc_locals;
    local x: Uint256 = Uint256(low=2000000000000000000, high=0);
    local y: Uint256 = Uint256(low=4, high=0);
    let (WAD) = FixedPointMathLib.WAD();

    let expectedResult = Uint256(low=16000000000000000000, high=0);

    let (res) = FixedPointMathLib.fpow(x, y, WAD);
    %{
        print(f"res: {ids.res.low + ids.res.high}")
    %}

    assert res = expectedResult;

    return ();
}

@external
func test_fpow_2{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}() {
    alloc_locals;
    local x: Uint256 = Uint256(low=101000000000000000000, high=0);
    local n: Uint256 = Uint256(low=2, high=0);
    let (baseUnit) = FixedPointMathLib.WAD();

    let expectedResult = Uint256(low=10201000000000000000000, high=0);

    let (res) = FixedPointMathLib.fpow(x, n, baseUnit);

    assert res = expectedResult;

    return ();
}