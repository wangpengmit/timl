pragma solidity ^0.4.7;
import "remix_tests.sol"; // this import is automatically injected by Remix.
import "./EtherDelta.sol";

contract test1 {
   
    EtherDelta contractToTest;
    constructor() {
      contractToTest = new EtherDelta(0xca35b7d915458ef540ade6068dfe2f44e8fa733c,
                                      0xca35b7d915458ef540ade6068dfe2f44e8fa733c,
                                      0xca35b7d915458ef540ade6068dfe2f44e8fa733c,
                                      1, 1, 1);
    }
    
    function checkTrade () public {
      /* contractToTest.trade(0x14723a09acff6d2a60dcdf7aa4aff308fddc160c, */
      /*                      0x10, */
      /*                      0x4b0897b0513fdc7c541b6d9d7e929c4e5364d2db, */
      /*                      0x10, */
      /*                      0xffffffffffff, */
      /*                      0, */
      /*                      0x583031d1113ad414f02576bd6afabfb302140225, */
      /*                      0, */
      /*                      0x00, */
      /*                      0x00, */
      /*                      5); */
      
      contractToTest.balanceOf(0x14723a09acff6d2a60dcdf7aa4aff308fddc160c,0xca35b7d915458ef540ade6068dfe2f44e8fa733c);
      
  //      Assert.equal(contractToTest.tokens(0x14723a09acff6d2a60dcdf7aa4aff308fddc160c,0xca35b7d915458ef540ade6068dfe2f44e8fa733c), 0x1b, "1");
  //      Assert.equal(contractToTest.tokens(0x4b0897b0513fdc7c541b6d9d7e929c4e5364d2db,0x583031d1113ad414f02576bd6afabfb302140225), 0x1b, "2");
    }
    
    /* function checkWinninProposalWithReturnValue () public constant returns (bool) { */
    /*     return contractToTest.winningProposal() == 1; */
    /* } */
}
