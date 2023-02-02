using MocksETH as sETHToken
using MockStakeHouseRegistry as StakeHouseRegistry
using MockStakeHouseUniverse as StakeHouseUniverse



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
    owner() returns (address) envfree
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

/** 
Title: Deregistering inactive knot always reverts
Description: 
When the liquid staking manager (Syndicate owner) calls deRegisterKnots to deregister a knot, 
and if the knot is inactive, the function will always revert.
Check: https://github.com/koolexcrypto/2023-01-blockswap-fv-private/issues/1
**/
rule deregisterInactiveKnotShouldSucceed()
{
    env e;
    bytes32 knot;
    
    require e.msg.sender == owner();
    require e.msg.value == 0;
    // safe assumptions 
    require StakeHouseUniverse.memberKnotToStakeHouse(knot) != 0;
    require isKnotRegistered(knot);
    require !isNoLongerPartOfSyndicate(knot);
    require accumulatedETHPerCollateralizedSlotPerKnot() == 0;
    require totalETHProcessedPerCollateralizedKnot(knot) == 0;
    require totalFreeFloatingShares() == 0;
    require sETHTotalStakeForKnot(knot) == 0;
    require lastSeenETHPerCollateralizedSlotPerKnot() == 0;
    require totalClaimed() == 0;
    require getEthBalance(currentContract) == 0;
    require numberOfRegisteredKnots() == 1; 

    deRegisterKnots@withrevert(e,knot);
    bool reverted = lastReverted;

    assert !StakeHouseRegistry.active(knot) => !reverted;
}


/**
Title: TotalFreeFloatingShares deduction for inactive knots
Description: 
If a knot went inactive in the stakehouse, 
and a user unstake his/her sETH balance before deregistering the knot,
The Syndicate deducts this amount from TotalFreeFloatingShares which is not supposed to occur.
Check: https://github.com/koolexcrypto/2023-01-blockswap-fv-private/issues/2
*/
rule totalFreeFloatingSharesCountActiveKnotsOnly()
{
    
    env e;
    bytes32 knot;
    address staker; 
    uint256 amount;
    require amount > 0;

    uint256 totalFreeFloatingShares = totalFreeFloatingShares();
    bool isKnotActive = StakeHouseRegistry.active(knot);

    unstake(e,staker,staker,knot,amount);
    uint256 totalFreeFloatingSharesAfter = totalFreeFloatingShares();

    assert !isKnotActive =>  totalFreeFloatingShares == totalFreeFloatingSharesAfter, "totalFreeFloatingShares deducted by an inactive knot";

}


