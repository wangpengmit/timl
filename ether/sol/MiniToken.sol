pragma solidity ^0.4.24;

contract MyToken {
    /* This creates an array with all balances */
    mapping (address => uint256) private balanceOf;

    /* Initializes contract with initial supply tokens to the creator of the contract */
    constructor (
        uint256 initialSupply
        ) public {
        balanceOf[msg.sender] = initialSupply;              // Give the creator all initial tokens
    }

    /* Send coins */
    function transfer(address _to, uint256 _value) public {
        require(balanceOf[msg.sender] >= _value);           // Check if the sender has enough
        require(balanceOf[_to] + _value >= balanceOf[_to]); // Check for overflows
        /* uint8 a = 100; */
        balanceOf[msg.sender] -= _value;                    // Subtract from the sender
        balanceOf[_to] += _value /* + a */;                           // Add the same to the recipient
    }
}
