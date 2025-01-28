// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console2 as console} from "../../lib/forge-std/src/Test.sol";
import {Constants} from "./Constants.sol";

struct Log {
    bytes32[] topics;
    bytes data;
    address emitter;
}

contract LogsTest is Test {
    event LogTopic1(uint256 indexed topic1, bytes data);

    event LogTopic12(
        uint256 indexed topic1,
        uint256 indexed topic2,
        bytes data
    );

    function testRecordAndGetLogs() public {
        bytes memory testData0 = "Some data";
        bytes memory testData1 = "Other data";

        (bool success, ) = Constants.CHEATCODE_ADDRESS.call(
            abi.encodeWithSignature("recordLogs()")
        );

        require(success, "recordLogs failed");

        emit LogTopic1(10, testData0);
        emit LogTopic12(20, 30, testData1);

        (bool success2, bytes memory rawData) = Constants
            .CHEATCODE_ADDRESS
            .call(abi.encodeWithSignature("getRecordedLogs()"));

        bytes memory data = trimReturnBytes(rawData);
        string memory dataString = string(data);
        console.log("dataString", dataString);
    }

    function trimReturnBytes(
        bytes memory rawData
    ) internal pure returns (bytes memory) {
        uint256 lengthStartingPos = rawData.length - 32;
        bytes memory lengthSlice = new bytes(32);
        for (uint256 i = 0; i < 32; i++) {
            lengthSlice[i] = rawData[lengthStartingPos + i];
        }
        uint256 length = abi.decode(lengthSlice, (uint256));
        bytes memory data = new bytes(length);
        for (uint256 i = 0; i < length; i++) {
            data[i] = rawData[i];
        }
        return data;
    }
}
