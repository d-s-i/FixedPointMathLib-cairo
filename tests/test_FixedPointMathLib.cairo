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

// @external
// func test_sqrt{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}() {
//     alloc_locals;
//     local x: Uint256 = Uint256(low=25000000000000000000, high=0);
//     // local x: Uint256 = Uint256(low=25, high=0);

//     let (test) = uint256_sqrt(x);
//     %{
//         print(f"uint256_sqrt res: {ids.test.low + ids.test.high}")
//     %}

//     let expectedResult = Uint256(low=5000000000, high=0);
//     // let expectedResult = Uint256(low=5, high=0);

//     // let (res)= FixedPointMathLib.sqrt(x);
//     let (res)= sqrt(x);
//     %{
//         print(f"res: {ids.res.low + ids.res.high}")
//     %}

//     assert res = expectedResult;

//     return ();
// }

    // func sqrt{syscall_ptr: felt*, pedersen_ptr: HashBuiltin*, range_check_ptr: felt}(x: Uint256) -> (res: Uint256) {
    //     alloc_locals;

    //     let borders: Uint256* = alloc();
    //     assert borders[0] = Uint256(low=0, high=1);
    //     assert borders[1] = Uint256(low=18446744073709551616, high=0);
    //     assert borders[2] = Uint256(low=4294967296, high=0);
    //     assert borders[3] = Uint256(low=65536, high=0);
    //     assert borders[4] = Uint256(low=256, high=0);
    //     assert borders[5] = Uint256(low=16, high=0);
    //     assert borders[6] = Uint256(low=8, high=0);

    //     let shiftingValues: felt* = alloc();
    //     assert shiftingValues[0] = 128;
    //     assert shiftingValues[1] = 64;
    //     assert shiftingValues[2] = 64;
    //     assert shiftingValues[3] = 32;
    //     assert shiftingValues[4] = 32;
    //     assert shiftingValues[5] = 16;
    //     assert shiftingValues[6] = 16;
    //     assert shiftingValues[7] = 8;
    //     assert shiftingValues[8] = 8;
    //     assert shiftingValues[9] = 4;
    //     assert shiftingValues[10] = 4;
    //     assert shiftingValues[11] = 2;
    //     assert shiftingValues[12] = 0;
    //     assert shiftingValues[13] = 1;

    //     let (temp_y, temp_z) = FixedPointMathLib._assignYAndZForSQRT(
    //         borders_len=7,
    //         borders=borders,
    //         y=x, 
    //         z=Uint256(low=1, high=0),
    //         shiftingValues_len=14,
    //         shiftingValues=shiftingValues
    //     );
    //     %{
    //         print(f"temp_y: {ids.temp_y.low + ids.temp_y.high}")
    //         print(f"temp_z: {ids.temp_z.low + ids.temp_z.high}")
    //     %}

    //     let (z) = FixedPointMathLib._shiftZ(7, x, temp_z);
    //     %{
    //         print(f"z: {ids.z.low + ids.z.high}")
    //     %}
    //     let (zRoundDown, zRoundDownRem) = uint256_unsigned_div_rem(x, z);

    //     let (zRoundDownLower) = uint256_lt(zRoundDown, z);
    //     if(zRoundDownLower == TRUE) {
    //         %{
    //             print(f"returning zRoundDown: {ids.zRoundDown.low + ids.zRoundDown.high}")
    //         %}
    //         return (res=zRoundDown);
    //     }
    //     %{
    //         print(f"returning z: {ids.z.low + ids.z.high}")
    //     %}
    //     return (res=z);
    // }