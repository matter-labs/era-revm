// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console2 as console} from "../lib/forge-std/src/Test.sol";

address constant CHEATCODE_ADDRESS = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;

contract CheatcodeDealTest is Test {
    address constant TEST_ADDRESS = 0x6Eb28604685b1F182dAB800A1Bfa4BaFdBA8a79a;
    uint256 constant NEW_BALANCE = 10;

    function test_deal() public {
        uint256 balanceBefore = address(TEST_ADDRESS).balance;
        console.log("balance before:", balanceBefore);

        (bool success, ) = CHEATCODE_ADDRESS.call(
            abi.encodeWithSignature(
                "deal(address,uint256)",
                TEST_ADDRESS,
                NEW_BALANCE
            )
        );
        uint256 balanceAfter = address(TEST_ADDRESS).balance;
        console.log("balance after :", balanceAfter);

        require(balanceAfter == NEW_BALANCE, "balance mismatch");
        require(balanceAfter != balanceBefore, "balance unchanged");
        require(success, "deal failed");
        console.log("failed?", failed());
    }
}

contract CheatcodeRollTest is Test {
    address constant TEST_ADDRESS = 0x6Eb28604685b1F182dAB800A1Bfa4BaFdBA8a79a;
    uint256 constant NEW_BLOCK_NUMBER = 10;

    function test_roll() public {
        uint256 initialBlockNumber = block.number;
        console.log("blockNumber before:", initialBlockNumber);

        require(
            NEW_BLOCK_NUMBER != initialBlockNumber,
            "block number must be different than current block number"
        );

        (bool success, ) = CHEATCODE_ADDRESS.call(
            abi.encodeWithSignature("roll(uint256)", NEW_BLOCK_NUMBER)
        );
        require(success, "roll failed");
        uint256 finalBlockNumber = block.number;
        console.log("blockNumber after :", finalBlockNumber);

        require(
            finalBlockNumber == NEW_BLOCK_NUMBER,
            "block number was not changed"
        );
        console.log("failed?", failed());
    }
}

contract CheatcodeWarpTest is Test {
    uint256 constant NEW_BLOCK_TIMESTAMP = uint256(10000);

    function test_warp() public {
        uint256 initialTimestamp = block.timestamp;
        console.log("timestamp before:", initialTimestamp);
        require(
            NEW_BLOCK_TIMESTAMP != initialTimestamp,
            "timestamp must be different than current block timestamp"
        );

        (bool success, ) = CHEATCODE_ADDRESS.call(
            abi.encodeWithSignature("warp(uint256)", NEW_BLOCK_TIMESTAMP)
        );
        require(success, "warp failed");

        uint256 finalTimestamp = block.timestamp;
        console.log("timestamp after:", finalTimestamp);
        require(
            finalTimestamp == NEW_BLOCK_TIMESTAMP,
            "timestamp was not changed"
        );
    }
}

contract CheatcodeSetNonceTest is Test {
    address constant TEST_ADDRESS = 0x6Eb28604685b1F182dAB800A1Bfa4BaFdBA8a79a;
    uint256 constant NEW_NONCE = uint256(10000);

    function test_setNonce() public {
        (bool success, ) = CHEATCODE_ADDRESS.call(
            abi.encodeWithSignature(
                "setNonce(address,uint64)",
                TEST_ADDRESS,
                NEW_NONCE
            )
        );
        require(success, "setNonce failed");
        /// we should assert over the set nonce once we have a way to read it using getNonce
    }
}
