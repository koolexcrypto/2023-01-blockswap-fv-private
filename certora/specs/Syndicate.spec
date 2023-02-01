using MocksETH as sETHToken
using MockStakeHouseRegistry as StakeHouseRegistry
using MockStakeHouseUniverse as StakeHouseUniverse
using MockSlotSettlementRegistry as SlotSettlementRegistry


methods {
    //// Regular methods
    totalETHReceived() returns (uint256) envfree
    isKnotRegistered(bytes32) returns (bool) envfree
    numberOfRegisteredKnots() returns (uint256) envfree
    isNoLongerPartOfSyndicate(bytes32) returns (bool) envfree
    lastAccumulatedETHPerFreeFloatingShare(bytes32) returns (uint256) envfree
    totalClaimed() returns (uint256) envfree
    totalFreeFloatingShares() returns (uint256) envfree
    lastSeenETHPerFreeFloating() returns (uint256) envfree
    lastSeenETHPerCollateralizedSlotPerKnot() returns (uint256) envfree
    accumulatedETHPerCollateralizedSlotPerKnot() returns (uint256) envfree
    accumulatedETHPerFreeFloatingShare() returns (uint256) envfree
    priorityStakingEndBlock() returns (uint256) envfree
    isPriorityStaker(address) returns (bool) envfree
    getEthBalance(address) returns (uint256) envfree
    calculateETHForFreeFloatingOrCollateralizedHolders() returns (uint256) envfree
    getUnprocessedETHForAllCollateralizedSlot() returns (uint256) envfree
    claimedPerCollateralizedSlotOwnerOfKnot(bytes32,address) returns (uint256) envfree
    //// Resolving external calls
	// stakeHouseUniverse
	stakeHouseKnotInfo(bytes32) returns (address,address,address,uint256,uint256,bool) => DISPATCHER(true)
    // memberKnotToStakeHouse(bytes32) returns (address) => DISPATCHER(true) // not used directly by Syndicate
    // stakeHouseRegistry
    getMemberInfo(bytes32) returns (address,uint256,uint16,bool) => DISPATCHER(true) // not used directly by Syndicate
    // slotSettlementRegistry
	stakeHouseShareTokens(address) returns (address)  => DISPATCHER(true)
	currentSlashedAmountOfSLOTForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
	numberOfCollateralisedSlotOwnersForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
	getCollateralisedOwnerAtIndex(bytes32, uint256) returns (address) => DISPATCHER(true)
	totalUserCollateralisedSLOTBalanceForKnot(address, address, bytes32) returns (uint256) => DISPATCHER(true)
    
    // StakeHouseUniverse
    StakeHouseUniverse.memberKnotToStakeHouse(bytes32) returns (address) envfree
    // StakeHouseRegistry
    StakeHouseRegistry.active(bytes32) returns (bool) envfree

    // sETH
    sETHToken.balanceOf(address) returns (uint256) envfree
    // ERC20
    name()                                returns (string)  => DISPATCHER(true)
    symbol()                              returns (string)  => DISPATCHER(true)
    decimals()                            returns (string) envfree => DISPATCHER(true)
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
    sETHUserClaimForKnot(bytes32,address) returns (uint256) envfree

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

// ------------ FUNCTIONS -------------

/// Corrollary that can be used as requirement after sETH solvency is proven.
function sETHSolvencyCorrollary(address user1, address user2, bytes32 knot) returns bool {
    return sETHStakedBalanceForKnot(knot,user1) + sETHStakedBalanceForKnot(knot,user2) <= sETHTotalStakeForKnot(knot);
}

// ------------ DEFINITIONS -------------

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


// ------------ GHOSTS -------------

ghost mapping(bytes32 => uint256) ghostsETHTotalStakeForKnot;


// ------------ HOOKS -------------

hook Sstore sETHStakedBalanceForKnot[KEY bytes32 knot][KEY address user] uint256 staked (uint256 old_staked) STORAGE {
  ghostsETHTotalStakeForKnot[knot] = ghostsETHTotalStakeForKnot[knot] + staked - old_staked;
}


// ------------ RULES -------------



// ------------ KNOT REGISTERATION -------------

/**
 * An unregistered knot can not be deregistered.
 */
rule canNotDegisterUnregisteredKnot(){
    bytes32 knot; env e;
    require !isKnotRegistered(knot);

    deRegisterKnots@withrevert(e, knot);

    assert lastReverted, "deRegisterKnots must revert if knot is not registered";
}

/**
* numberOfRegisteredKnots holds upon register and deregieter
*/
rule numberOfRegisteredKnotsHolds(bytes32 knot)
{
    env e;
    
    uint256 registeredKnotsBefore = numberOfRegisteredKnots();

    registerKnotsToSyndicate(e,knot);
    deRegisterKnots(e,knot);

    uint256 registeredKnotsAfter = numberOfRegisteredKnots();

    assert registeredKnotsBefore == registeredKnotsAfter, "numberOfRegisteredKnots doesn't hold as expected";

}

/**
* can not register already registered knot
*/
rule knotCanNotBeRegisteredTwice()
{
    env e;
    bytes32 knot;

    registerKnotsToSyndicate(e,knot);
    registerKnotsToSyndicate@withrevert(e,knot);
    bool reverted = lastReverted;

    assert reverted, "Knot was registered twice";
}

/**
* can not register already registered knot
*/
rule knotCanNotBeRegisteredIfHasNoOwners()
{
    env e;
    bytes32 knot;
    require SlotSettlementRegistry.numberOfCollateralisedSlotOwnersForKnot(e,knot) == 0;
    
    registerKnotsToSyndicate@withrevert(e,knot);
    bool reverted = lastReverted;

    assert reverted, "Knot was registered with no SLOT owners";
}

/**
* can not register inactive knot
*/
rule inactiveKnotCanNotBeRegistered()
{
    env e;
    bytes32 knot;
    require !StakeHouseRegistry.active(knot);

    registerKnotsToSyndicate@withrevert(e,knot);
    bool reverted = lastReverted;

    assert reverted, "Inactive knot was registered";
}

/** 
* numberOfRegisteredKnotsHoldsOnRegisterDeregieter holds 
*/
rule numberOfRegisteredKnotsHoldsOnRegisterDeregieter(method f,bytes32 knot,bytes32 knot2) filtered {
    f -> notRegisterationMethod(f)
}{
    env e;
    require isNoLongerPartOfSyndicate(knot);
    require isNoLongerPartOfSyndicate(knot2);

    uint256 registeredKnotsBefore = numberOfRegisteredKnots();

    if (f.selector == updateCollateralizedSlotOwnersAccruedETH(bytes32).selector) {
        updateCollateralizedSlotOwnersAccruedETH(e,knot);
    } else if (f.selector == batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32).selector) {
        batchUpdateCollateralizedSlotOwnersAccruedETH(e,knot);
    } else if (f.selector == batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32).selector) {
        batchUpdateCollateralizedSlotOwnersAccruedETH(e,knot,knot2);
    } else if (f.selector == claimAsCollateralizedSLOTOwner(address,bytes32).selector) {
        address addr;
        claimAsCollateralizedSLOTOwner(e,addr,knot);
    } else if (f.selector == claimAsCollateralizedSLOTOwner(address,bytes32,bytes32).selector) {
        address addr;
        claimAsCollateralizedSLOTOwner(e,addr,knot,knot2);
    } else {
        calldataarg args;
        f(e, args);
    }

    uint256 registeredKnotsAfter = numberOfRegisteredKnots();

    assert registeredKnotsBefore == registeredKnotsAfter, "numberOfRegisteredKnots doesn't hold as expected";

}


// ------------ INVARIANTS -------------

/**
* Staker invariants (e.g.sETHUserClaimForKnot and sETHStakedBalanceForKnot ) must never decrease via any action taken by another actor.
*/
rule stakerInvariantsMustNeverDecrease(method f,bytes32 knot,address staker) filtered {
    f -> notHarnessCall(f)
}{
    env e;
    require e.msg.sender != staker;

    uint256 sETHUserClaimForKnot = sETHUserClaimForKnot(knot,staker);
    uint256 sETHStakedBalanceForKnot = sETHStakedBalanceForKnot(knot,staker);

    calldataarg args;
    f(e, args);

    uint256 sETHUserClaimForKnotAfter = sETHUserClaimForKnot(knot,staker);
    uint256 sETHStakedBalanceForKnotAfter = sETHStakedBalanceForKnot(knot,staker);

    assert sETHUserClaimForKnot <= sETHUserClaimForKnotAfter, "sETHUserClaimForKnot doesn't hold as expected";
    assert sETHStakedBalanceForKnot <= sETHStakedBalanceForKnotAfter, "sETHStakedBalanceForKnot doesn't hold as expected";

}


/**
sETHTotalStakeForKnot must never go above 12 ether
**/
rule totalStakeForKnotMaxIs12Ether(method f,bytes32 knot) filtered {
    f -> notHarnessCall(f)
}{
    require sETHTotalStakeForKnot(knot) <= 12^18;

    env e;
    calldataarg args;
    f(e, args);

    assert sETHTotalStakeForKnot(knot) <= 12^18;
}

/** 
* totalFreeFloatingShares counts non deregistered knots only
*/
rule totalFreeFloatingSharesCountNonDeregisteredKnotsOnly()
{
    
    env e;
    bytes32 knot;
    address staker; 
    uint256 amount;
    require amount > 0;
    
    uint256 totalFreeFloatingShares = totalFreeFloatingShares();
    bool isDeregistered = isNoLongerPartOfSyndicate(knot);

    unstake(e,staker,staker,knot,amount);
    uint256 totalFreeFloatingSharesAfter = totalFreeFloatingShares();

    assert isDeregistered =>  totalFreeFloatingShares == totalFreeFloatingSharesAfter, "totalFreeFloatingShares deducted by a deregistered knot";
    assert !isDeregistered =>  totalFreeFloatingShares-amount == totalFreeFloatingSharesAfter, "totalFreeFloatingShares deducted by a deregistered knot";

}


/**
* validate sETHStakedBalanceForKnot is updated when sETHStakedBalanceForKnot gets updated for a user
**/
rule sETHStakedBalanceForKnotInvariant(method f)  filtered {
    f -> notHarnessCall(f)
}{
  env e;
  bytes32 knot;
  require sETHTotalStakeForKnot(knot) == ghostsETHTotalStakeForKnot[knot];
  calldataarg arg;
  f(e, arg);
  assert sETHTotalStakeForKnot(knot) == ghostsETHTotalStakeForKnot[knot];
}

/**
* Check Correctness of amount of ETH per collateralized share that hasn't yet been allocated to each share
**/
rule CorrectAmountOfUnprocessedETHForAllCollateralizedSlot() {
    mathint calcETH = calculateETHForFreeFloatingOrCollateralizedHolders();
    mathint lastSeenETH = lastSeenETHPerCollateralizedSlotPerKnot();
    mathint registeredKnots = numberOfRegisteredKnots();
    mathint UnprocessedETH = getUnprocessedETHForAllCollateralizedSlot();
    assert UnprocessedETH == (calcETH-lastSeenETH)/registeredKnots;
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
 * Address 0 must have zero sETH balance.
 */
invariant addressZeroHasNoBalance()
    sETHToken.balanceOf(0) == 0



 // ------------ OTHER -------------

// /** LATER
// * initialize can not be called more than once (over the implementation contract)
// */
// rule initializeCanBeCalledOnlyOnce()
// {
//     env e;
//     address _contractOwner;
//     uint256 _priorityStakingEndBlock;
//     address _priorityStaker;
//     bytes32 knot;
//     bool initialized = getInitialized();
//     initialize@withrevert(e,_contractOwner,_priorityStakingEndBlock,_priorityStaker,knot);
//     bool reverted = lastReverted;
//     assert initialized => reverted, "Contract was initialized twice";
// }
   

/**
* transfer ownership upon initialization  
*/
rule transferOwnershipOnInitialization()
{
    env e;
    address _contractOwner;
    uint256 _priorityStakingEndBlock;
    address _priorityStaker;
    bytes32 knot;

    initialize(e,_contractOwner,_priorityStakingEndBlock,_priorityStaker,knot);

    assert owner(e) == _contractOwner, "Contract owner hasn't changed";
}


/**
* accumulatedETHPerFreeFloatingShare should be updated only when totalFreeFloatingShares bigger than zero
*/
rule updateAccumulatedETHPerFreeFloatingShare()
{
    env e;
    require numberOfRegisteredKnots() > 0;
    uint256 NewAccumulatedETH = calculateNewAccumulatedETHPerFreeFloatingShare(e);
    uint256 accumulatedETHPerFreeFloatingShare = accumulatedETHPerFreeFloatingShare();
    uint256 totalFreeFloatingShares = totalFreeFloatingShares();
    updateAccruedETHPerShares(e);
    uint256 accumulatedETHPerFreeFloatingShareAfter = accumulatedETHPerFreeFloatingShare();

    assert totalFreeFloatingShares > 0 => accumulatedETHPerFreeFloatingShareAfter == accumulatedETHPerFreeFloatingShare + NewAccumulatedETH, "";
    assert totalFreeFloatingShares == 0 => accumulatedETHPerFreeFloatingShareAfter == accumulatedETHPerFreeFloatingShare, "";

}