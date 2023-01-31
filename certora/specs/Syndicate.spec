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

/**
* validate sETHStakedBalanceForKnot is updated when sETHStakedBalanceForKnot gets updated for a user
**/
rule sETHStakedBalanceForKnotInvariant(method f) {
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

/** -> should check this later
* numberOfRegisteredKnotsHoldsOnRegisterDeregieter holds 
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

/**
* Staker invariants (e.g.sETHUserClaimForKnot and sETHStakedBalanceForKnot ) must never decrease via any action taken by another actor.
*/
rule stakerInvariantsMustNeverDecrease(method f,bytes32 blsPubKey,address staker)
{
    env e;
    require e.msg.sender != staker;

    uint256 sETHUserClaimForKnot = sETHUserClaimForKnot(blsPubKey,staker);
    uint256 sETHStakedBalanceForKnot = sETHStakedBalanceForKnot(blsPubKey,staker);

    calldataarg args;
    f(e, args);

    uint256 sETHUserClaimForKnotAfter = sETHUserClaimForKnot(blsPubKey,staker);
    uint256 sETHStakedBalanceForKnotAfter = sETHStakedBalanceForKnot(blsPubKey,staker);

    assert sETHUserClaimForKnot <= sETHUserClaimForKnotAfter, "sETHUserClaimForKnot doesn't hold as expected";
    assert sETHStakedBalanceForKnot <= sETHStakedBalanceForKnotAfter, "sETHStakedBalanceForKnot doesn't hold as expected";

}


/**
* Staker gets exactly the same sETH token amount upon stake and unstake.
*/
rule StakerReceivesExactsETH(method f,bytes32 blsPubKey,address staker,uint256 amount)
{
    env e;
    require e.msg.sender == staker;
    require sETHToken.balanceOf(staker) == amount;

    stake(e,blsPubKey,amount,staker);
    unstake(e,staker,staker,blsPubKey,amount);

    assert sETHToken.balanceOf(staker) == amount, "Staker got more/less sETH";

}


/**
 * Staker receives sETH token upon unstake.
 */
rule receivesETHOnUnstake()
{
    
    env e;
    bytes32 knot;
    address staker;
    uint256 amount;

    require e.msg.sender == staker;
    require e.msg.value == 0;

    uint256 amountBefore = sETHToken.balanceOf(staker);

    unstake(e,staker,staker,knot,amount);

    uint256 amountAfter = sETHToken.balanceOf(staker);

    assert amountAfter == amountBefore + amount, "Staker didn't receive the expected sETH";
}


/**
 * revert if transferring sETH token fails upon unstake.
 */
rule revertIfsETHTransferFailOnUnstake()
{
    
    env e;
    bytes32 knot;
    uint256 amount;

    // Safe assumptions
    require e.msg.sender != 0;
    require currentContract != 0;
    require e.msg.sender != currentContract;
    require e.msg.value == 0;
    require sETHStakedBalanceForKnot(knot,e.msg.sender) >= amount;
    // This condition just to cause transfer failure 
    require sETHToken.balanceOf(currentContract) < amount;

    uint256 stakerBalanceBefore = sETHToken.balanceOf(e.msg.sender);
    uint256 contractBalanceBefore = sETHToken.balanceOf(currentContract);

    unstake@withrevert(e,e.msg.sender,e.msg.sender,knot,amount);
    bool reverted = lastReverted;

    assert sETHToken.balanceOf(e.msg.sender) != stakerBalanceBefore + amount => reverted , "unstake didn't revert on failed transfer";
    assert sETHToken.balanceOf(currentContract) != contractBalanceBefore - amount => reverted , "unstake didn't revert on failed transfer";

}

/**
 * revert if transferring sETH token fails upon stake.
 */
rule revertIfsETHTransferFailOnStake()
{
    
    env e;
    bytes32 knot;
    uint256 amount;

    // Safe assumptions
    require e.msg.sender != 0;
    require currentContract != 0;
    require e.msg.sender != currentContract;
    require e.msg.value == 0;
    require amount > 1000000000;
    require isKnotRegistered(knot) && !isNoLongerPartOfSyndicate(knot);
    require priorityStakingEndBlock() <= e.block.number;
    require amount + sETHTotalStakeForKnot(knot) <= 12000000000000000000;
    // This condition just to cause transfer failure 
    require sETHToken.balanceOf(e.msg.sender) < amount;

    uint256 stakerBalanceBefore = sETHToken.balanceOf(e.msg.sender);
    uint256 contractBalanceBefore = sETHToken.balanceOf(currentContract);

    stake@withrevert(e,knot,amount,e.msg.sender);
    bool reverted = lastReverted;

    assert sETHToken.balanceOf(e.msg.sender) != stakerBalanceBefore - amount => reverted , "unstake didn't revert on failed transfer";
    assert sETHToken.balanceOf(currentContract) != contractBalanceBefore + amount => reverted , "unstake didn't revert on failed transfer";

}

/**
 * Staker receives uncalimed share of ETH when claiming.
 */
rule stakerReceivesExactUnclaimedETHWhenClaiming()
{
    
    env e;
    bytes32 knot;
    uint256 amount;
    
    // Safe Assumptions
    require e.msg.sender != 0;
    require e.msg.sender != currentContract;
    require e.msg.value == 0;
    updateAccruedETHPerShares(e); // assuming this was called before, otherwise, it is a issue.
    uint256 unclaimed = calculateUnclaimedFreeFloatingETHShare(e,knot, e.msg.sender);
    uint256 etherBalance = getEthBalance(e.msg.sender);
    claimAsStaker(e,e.msg.sender,knot);

    uint256 etherBalanceAfter = getEthBalance(e.msg.sender);

    assert etherBalanceAfter == etherBalance + unclaimed ,"Staker didn't receive exact ether share";

}

/**
 * unclaimed User Share must be zero after claiming as a staker.
 */
rule zeroUnclaimedUserShareAfterClaiming()
{
    
    env e;
    bytes32 knot;
    uint256 amount;
    
    // Safe Assumptions
    require e.msg.sender != 0;
    require e.msg.sender != currentContract;
    require e.msg.value == 0;

    uint256 unclaimed = calculateUnclaimedFreeFloatingETHShare(e,knot, e.msg.sender);

    claimAsStaker(e,e.msg.sender,knot);

    uint256 unclaimedAfter = calculateUnclaimedFreeFloatingETHShare(e,knot, e.msg.sender);

    assert unclaimed > 0 => unclaimedAfter == 0 ,"Unclaimed User Share is not zero after claiming";

}

/**
 * Staker receives uncalimed share of ETH.
 */
rule stakerReceivesUnclaimedUserShareOnUnstake()
{    
    env e;
    bytes32 knot;
    uint256 amount;
    
    require e.msg.sender != 0;
    require e.msg.sender != currentContract;
    require e.msg.value == 0;

    updateAccruedETHPerShares(e);
    uint256 unclaimed = calculateUnclaimedFreeFloatingETHShare(e,knot, e.msg.sender);
    uint256 etherBalance = getEthBalance(e.msg.sender);

    unstake(e,e.msg.sender,e.msg.sender,knot,amount);

    uint256 etherBalanceAfter = getEthBalance(e.msg.sender);

    assert etherBalanceAfter == etherBalance + unclaimed ,"Staker didn't receive ether share";

}

/**
* When staking block is in future, only those listed in the priority staker list can stake sETH
*/
rule onlyPriorityStakerStake()
{
    
    env e;
    bytes32 knot;
    address staker; // on-behalf
    uint256 amount;

    require priorityStakingEndBlock() > e.block.number;
    require !isPriorityStaker(staker);
    require e.msg.value == 0;

    stake@withrevert(e,knot,amount,staker);

    assert lastReverted, "stake must revert if block in future and staker is not priority";

}



/**
sETHTotalStakeForKnot must never go above 12 ether
**/
rule totalStakeForKnotMaxIs12Ether(method f,bytes32 knot)
{
    require sETHTotalStakeForKnot(knot) <= 12^18;

    env e;
    calldataarg args;
    f(e, args);

    assert sETHTotalStakeForKnot(knot) <= 12^18;
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


/** NOT DONE YET **
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
*  Staking to a zero address reverts
*/
rule stakeToZeroAddreessRevert()
{
    
    env e;
    bytes32 knot;
    address staker; // on-behalf
    uint256 amount;


    stake@withrevert(e,knot,amount,staker);
    bool reverted = lastReverted;

    assert staker == 0 => lastReverted, "stake must revert if address is zero";

}


/**
*  Staking with too small sETH amount reverts
*/
rule stakingTooSmallAmountRevert()
{
    
    env e;
    bytes32 knot;
    address staker; // on-behalf
    uint256 amount;


    stake@withrevert(e,knot,amount,staker);
    bool reverted = lastReverted;

    assert amount < 10^9 => lastReverted, "stake must revert if amount less than 1";

}

/**
*  Stake reverts if knot doesn't belong to a stakehouse
*/
rule stakingUnassociatedKnotRevert()
{
    
    env e;
    bytes32 knot;
    address staker; // on-behalf
    uint256 amount;


    stake@withrevert(e,knot,amount,staker);
    bool reverted = lastReverted;
    address stakeHouse = getStakeHouseForKnot(e,knot);

    assert stakeHouse == 0 => lastReverted, "stake must revert if knot is not associated with a stakehouse";

}

/**
 * unstake revert if amount is bigger than staked balance.
 */
rule revertIfsETHAmountBiggerThanStakedBalance()
{
    
    env e;
    bytes32 knot;
    uint256 amount;
    uint256 staked = sETHStakedBalanceForKnot(knot,e.msg.sender);
    unstake@withrevert(e,e.msg.sender,e.msg.sender,knot,amount);
    bool reverted = lastReverted;

    assert staked < amount => reverted , "unstake didn't revert when nothing is staked";

}


/**
*  Unstaking to a zero address reverts
*/
rule unstakeToZeroRecipientAddreessRevert()
{
    
    env e;
    bytes32 knot;
    address sETHRecipient; 
    address ETHRecipient; 
    uint256 amount;


    unstake@withrevert(e,ETHRecipient,sETHRecipient,knot,amount);
    bool reverted = lastReverted;

    assert sETHRecipient == 0 => lastReverted, "unstake must revert if sETH recipient address is zero";
    assert ETHRecipient == 0 => lastReverted, "unstake must revert if ETH recipient address is zero";

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
    assert !isDeregistered =>  totalFreeFloatingShares+amount == totalFreeFloatingSharesAfter, "totalFreeFloatingShares deducted by a deregistered knot";

}

/**
*  claimAsCollateralizedSLOTOwner to Syndicate or zero address reverts
*/
rule claimAsSLOTOwnerToZeroRecipientAddreessRevert()
{
    
    env e;
    bytes32 knot;
    address recipient; 

    claimAsCollateralizedSLOTOwner@withrevert(e,recipient,knot);
    bool reverted = lastReverted;

    assert recipient == 0 => lastReverted, "calim must revert if recipient address is zero";
    assert recipient == currentContract => lastReverted, "calim must revert if recipient address is Syndicate";

}


/**
*  claimAsCollateralizedSLOTOwner reverts for not registered knot
*/
rule claimAsSLOTOwnerToZeroRevertIfKnotNotRegistered()
{
    
    env e;
    bytes32 knot;
    address recipient;

    claimAsCollateralizedSLOTOwner(e,recipient,knot);


    assert !isKnotRegistered(knot) => false, "calim must always revert if knot unregistered";

}

/**
 * Address 0 must have zero sETH balance.
 */
invariant addressZeroHasNoBalance()
    sETHToken.balanceOf(0) == 0