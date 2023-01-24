using MocksETH as sETHToken

methods {
    //// Regular methods
    totalETHReceived() returns (uint256) envfree
    isKnotRegistered(bytes32) returns (bool) envfree
    numberOfRegisteredKnots() returns (uint256) envfree
    isNoLongerPartOfSyndicate(bytes32) returns (bool) envfree

    

    //// Resolving external calls
	// stakeHouseUniverse
	stakeHouseKnotInfo(bytes32) returns (address,address,address,uint256,uint256,bool) => DISPATCHER(true)
    memberKnotToStakeHouse(bytes32) returns (address) => DISPATCHER(true) // not used directly by Syndicate
    // stakeHouseRegistry
    getMemberInfo(bytes32) returns (address,uint256,uint16,bool) => DISPATCHER(true) // not used directly by Syndicate
    // slotSettlementRegistry
	stakeHouseShareTokens(address) returns (address)  => DISPATCHER(true)
	currentSlashedAmountOfSLOTForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
	numberOfCollateralisedSlotOwnersForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
	getCollateralisedOwnerAtIndex(bytes32, uint256) returns (address) => DISPATCHER(true)
	totalUserCollateralisedSLOTBalanceForKnot(address, address, bytes32) returns (uint256) => DISPATCHER(true)
    // sETH
    sETHToken.balanceOf(address) returns (uint256) envfree
    // ERC20
    name()                                returns (string)  => DISPATCHER(true)
    symbol()                              returns (string)  => DISPATCHER(true)
    decimals()                            returns (string)  => DISPATCHER(true)
    totalSupply()                         returns (uint256) => DISPATCHER(true)
    balanceOf(address)                    returns (uint256) => DISPATCHER(true)
    allowance(address,address)            returns (uint)    => DISPATCHER(true)
    approve(address,uint256)              returns (bool)    => DISPATCHER(true)
    transfer(address,uint256)             returns (bool)    => DISPATCHER(true)
    transferFrom(address,address,uint256) returns (bool)    => DISPATCHER(true)

    //// Harnessing
    // harnessed variables
    accruedEarningPerCollateralizedSlotOwnerOfKnot(bytes32,address) returns (uint256) envfree
    totalETHProcessedPerCollateralizedKnot(bytes32) returns (uint256) envfree
    sETHStakedBalanceForKnot(bytes32,address) returns (uint256) envfree
    sETHTotalStakeForKnot(bytes32) returns (uint256) envfree
    // harnessed functions
    deRegisterKnots(bytes32) 
    deRegisterKnots(bytes32,bytes32)
    stake(bytes32,uint256,address)
    stake(bytes32,bytes32,uint256,uint256,address)
    unstake(address,address,bytes32,uint256)
    unstake(address,address,bytes32,bytes32,uint256,uint256)
    claimAsStaker(address,bytes32)
    claimAsStaker(address,bytes32,bytes32)
    claimAsCollateralizedSLOTOwner(address,bytes32)
    claimAsCollateralizedSLOTOwner(address,bytes32,bytes32)
    registerKnotsToSyndicate(bytes32)
    registerKnotsToSyndicate(bytes32,bytes32)
    addPriorityStakers(address)
    addPriorityStakers(address,address)
    batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32)
    batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32)
}

/// We defined additional functions to get around the complexity of defining dynamic arrays in cvl. We filter them in 
/// normal rules and invariants as they serve no purpose.
definition notHarnessCall(method f) returns bool = 
    f.selector != batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32).selector
    && f.selector != batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32).selector
    && f.selector != deRegisterKnots(bytes32).selector
    && f.selector != deRegisterKnots(bytes32,bytes32).selector
    && f.selector != stake(bytes32,uint256,address).selector
    && f.selector != stake(bytes32,bytes32,uint256,uint256,address).selector
    && f.selector != unstake(address,address,bytes32,uint256).selector
    && f.selector != unstake(address,address,bytes32,bytes32,uint256,uint256).selector
    && f.selector != claimAsStaker(address,bytes32).selector
    && f.selector != claimAsStaker(address,bytes32,bytes32).selector
    && f.selector != claimAsCollateralizedSLOTOwner(address,bytes32).selector
    && f.selector != claimAsCollateralizedSLOTOwner(address,bytes32,bytes32).selector
    && f.selector != registerKnotsToSyndicate(bytes32).selector
    && f.selector != registerKnotsToSyndicate(bytes32,bytes32).selector
    && f.selector != addPriorityStakers(address).selector
    && f.selector != addPriorityStakers(address,address).selector;


definition notRegisterationMethod(method f) returns bool = 
    f.selector != claimAsCollateralizedSLOTOwner(address,bytes32[]).selector     
    && f.selector != batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32[]).selector     
    && f.selector != initialize(address,uint256,address[],bytes32[]).selector 
    && f.selector != registerKnotsToSyndicate(bytes32[]).selector 
    && f.selector != deRegisterKnots(bytes32[]).selector 
    && f.selector != registerKnotsToSyndicate(bytes32).selector 
    && f.selector != registerKnotsToSyndicate(bytes32,bytes32).selector
    && f.selector != deRegisterKnots(bytes32).selector
    && f.selector != deRegisterKnots(bytes32,bytes32).selector;


/// Corrollary that can be used as requirement after sETH solvency is proven.
function sETHSolvencyCorrollary(address user1, address user2, bytes32 knot) returns bool {
    return sETHStakedBalanceForKnot(knot,user1) + sETHStakedBalanceForKnot(knot,user2) <= sETHTotalStakeForKnot(knot);
}

// rule getGet() {
//     bytes32 in1; address in2;
//     uint256 out1 = accruedEarningPerCollateralizedSlotOwnerOfKnot(in1,in2);
//     bytes32 in3;
//     uint256 out2 = totalETHProcessedPerCollateralizedKnot(in3);
//     bytes32 in4; address in5;
//     uint256 out3 = sETHStakedBalanceForKnot(in4,in5);
//     bytes32 in6;
//     uint256 out4 = sETHTotalStakeForKnot(in6);
//     assert out1 + out2 + out3 + out4 < 100;
// }

/**
 * An unregistered knot can not be deregistered.
 */
rule canNotDegisterUnregisteredKnot(method f) filtered {
    f -> notHarnessCall(f)
} {
    bytes32 knot; env e;
    require !isKnotRegistered(knot);

    deRegisterKnots@withrevert(e, knot);

    assert lastReverted, "deRegisterKnots must revert if knot is not registered";
}

/**
 * Total ETH received must not decrease.
 */
rule totalEthReceivedMonotonicallyIncreases(method f) filtered {
    f -> notHarnessCall(f)
}{
    
    uint256 totalEthReceivedBefore = totalETHReceived();

    env e; calldataarg args;
    f(e, args);

    uint256 totalEthReceivedAfter = totalETHReceived();

    assert totalEthReceivedAfter >= totalEthReceivedBefore, "total ether received must not decrease";
}

/**
* numberOfRegisteredKnots holds 
*/
rule numberOfRegisteredKnotsHoldsOnRegisterDeregieter(method f,bytes32 blsPubKey,bytes32 blsPubKey2) filtered {
    f -> notRegisterationMethod(f)
}{
    env e;
    require isNoLongerPartOfSyndicate(blsPubKey);
    require isNoLongerPartOfSyndicate(blsPubKey2);

    uint256 registeredKnotsBefore = numberOfRegisteredKnots();

    if (f.selector == updateCollateralizedSlotOwnersAccruedETH(bytes32).selector) {
        updateCollateralizedSlotOwnersAccruedETH(e,blsPubKey);
    } else if (f.selector == batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32).selector) {
        batchUpdateCollateralizedSlotOwnersAccruedETH(e,blsPubKey);
    } else if (f.selector == batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32).selector) {
        batchUpdateCollateralizedSlotOwnersAccruedETH(e,blsPubKey,blsPubKey2);
    } else if (f.selector == claimAsCollateralizedSLOTOwner(address,bytes32).selector) {
        address addr;
        claimAsCollateralizedSLOTOwner(e,addr,blsPubKey);
    } else if (f.selector == claimAsCollateralizedSLOTOwner(address,bytes32,bytes32).selector) {
        address addr;
        claimAsCollateralizedSLOTOwner(e,addr,blsPubKey,blsPubKey2);
    } else {
        calldataarg args;
        f(e, args);
    }

    uint256 registeredKnotsAfter = numberOfRegisteredKnots();

    assert registeredKnotsBefore == registeredKnotsAfter, "numberOfRegisteredKnots doesn't hold as expected";

}

/**
* numberOfRegisteredKnots holds upon register and deregieter
*/
rule numberOfRegisteredKnotsHolds(method f,bytes32 blsPubKey)
{
    env e;
    
    uint256 registeredKnotsBefore = numberOfRegisteredKnots();

    registerKnotsToSyndicate(e,blsPubKey);
    deRegisterKnots(e,blsPubKey);

    uint256 registeredKnotsAfter = numberOfRegisteredKnots();

    assert registeredKnotsBefore == registeredKnotsAfter, "numberOfRegisteredKnots doesn't hold as expected";

}

// rule sETHRecipientBalanceIncreasesUponUnstake(method f,bytes32 blsPubKey,uint256 sETHAmount) {
//     env e; 

//     // require sETHAmount > 0;
//     // require sETHAmount < max_uint128;
//     // require sETHAmount < sETHToken.balanceOf(e.msg.sender);
//     // require sETHStakedBalanceForKnot(blsPubKey,e.msg.sender) >= sETHAmount;
//     // require e.msg.value == 0; // safe assumption as the function is not payable
//     // require e.msg.sender != 0;
//     // require e.msg.sender != currentContract;
//     // require lastSeenETHPerCollateralizedSlotPerKnot(e) == 1;
//     // require accumulatedETHPerCollateralizedSlotPerKnot(e) < max_uint128;
//     // require totalETHReceived() < max_uint128;
//     // require isKnotRegistered(blsPubKey);
//     // require numberOfRegisteredKnots 

//     // function stake(bytes[] calldata _blsPubKeys, uint256[] calldata _sETHAmounts, address _onBehalfOf) external {

//     // stake@withrevert(e, blsPubKey, sETHAmount, e.msg.sender);

// 	uint256 sETHBalanceBefore = sETHToken.balanceOf(e.msg.sender);

//     // unstake@withrevert(e, e.msg.sender, e.msg.sender, blsPubKey, sETHAmount);
//     // unstake(e, e.msg.sender, e.msg.sender, blsPubKey, sETHAmount);

//     uint256 sETHBalanceAfter = sETHToken.balanceOf(e.msg.sender);
//     assert sETHBalanceAfter == sETHBalanceBefore + sETHAmount, "Balance must increase";
// }

/**
 * Address 0 must have zero sETH balance.
 */
invariant addressZeroHasNoBalance()
    sETHToken.balanceOf(0) == 0