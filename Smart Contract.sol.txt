// SPDX-License-Identifier: MIT
pragma solidity ^0.6.0;
pragma experimental ABIEncoderV2;

contract LatencyTest {
    // 定义数据结构
    struct TestData {
        uint256 id;
        string content;
        uint256 timestamp;
    }
    
    // 存储所有测试数据
    TestData[] public testRecords;
    
    // 记录上传时间
    mapping(uint256 => uint256) public uploadTimes;
    
    // 上传数据并记录时间
    function uploadData(uint256 _id, string memory _content) public returns (uint256) {
        uint256 startTime = block.timestamp;
        
        TestData memory newData = TestData({
            id: _id,
            content: _content,
            timestamp: startTime
        });
        
        testRecords.push(newData);
        uploadTimes[_id] = startTime;
        
        return startTime;
    }
    
    // 获取数据上传的时间戳
    function getUploadTime(uint256 _id) public view returns (uint256) {
        return uploadTimes[_id];
    }
    
    // 获取所有测试记录
    function getAllRecords() public view returns (TestData[] memory) {
        return testRecords;
    }
}
