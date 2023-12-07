// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console2 as console} from "../../lib/forge-std/src/Test.sol";
import {Constants} from "./Constants.sol";

contract FsTest is Test {
    function testReadFile() public {
        string memory path = "src/fixtures/File/read.txt";

        (bool success, bytes memory rawData) = Constants.CHEATCODE_ADDRESS.call(
            abi.encodeWithSignature("readFile(string)", path)
        );
        require(success, "readFile failed");

        bytes memory data = trimReturnBytes(rawData);

        require(
            keccak256(data) ==
                keccak256("hello readable world\nthis is the second line!\n"),
            "read data did not match expected data"
        );
        console.log("failed?", failed());
    }

    function testWriteFile() public {
        string memory path = "src/fixtures/File/write_file.txt";
        string memory writeData = "hello writable world";

        (bool success, ) = Constants.CHEATCODE_ADDRESS.call(
            abi.encodeWithSignature("writeFile(string,string)", path, writeData)
        );
        require(success, "writeFile failed");

        bytes memory readRawData;
        (success, readRawData) = Constants.CHEATCODE_ADDRESS.call(
            abi.encodeWithSignature("readFile(string)", path)
        );
        require(success, "readFile failed");

        bytes memory readData = trimReturnBytes(readRawData);

        require(
            keccak256(readData) == keccak256(bytes(writeData)),
            "read data did not match write data"
        );
        console.log("failed?", failed());
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
