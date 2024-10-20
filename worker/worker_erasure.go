package worker

import (
	"encoding/json"
	"fmt"
	"time"

	"github.com/fowlerlee/orchestration/common"
)

func (w *Worker) EncodeAndSendData() error {
	w.Lock()
	defer w.Unlock()
	rpcMethod := "Manager.BackupWorkerData"

	data, err := json.Marshal(w.kVStore)
	if err != nil {
		return err
	}

	w.EncodedData, err = common.EncodeXOR(data)
	if err != nil {
		return err
	}

	args := &common.BackupDataArgs{
		WorkerID:    w.ID.String(),
		EncodedData: w.EncodedData,
	}
	reply := &common.BackupDataReply{}

	ok := common.RpcCall(w.managerIP, rpcMethod, args, reply)
	if !ok {
		return fmt.Errorf("failed to call %v rpc methods from Worker %v", rpcMethod, w.Address)
	}
	return nil
}

func (w *Worker) PeriodicBackup() {
	ticker := time.NewTicker(5 * time.Second) // set to 10 minutes to save bandwidth
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			err := w.EncodeAndSendData()
			if err != nil {
				fmt.Printf("error backing up data: %v\n", err)
			}
		case <-w.shutdown:
			return
		}
	}
}

func (w *Worker) RecoverDataFromManager() error {
	w.Lock()
	defer w.Unlock()

	args := &common.BackupDataArgs{
		WorkerID: w.ID.String(),
	}
	reply := &common.BackupDataReply{}

	ok := common.RpcCall(w.managerIP, "Manager.GetWorkerDataAfterRecovery", args, reply)
	if !ok {
		fmt.Println("failed to get Worker data from manager")
	}

	if !reply.Success {
		fmt.Println("failed to recover date from manager")
	}

	var recoveredData map[string]string
	err := json.Unmarshal(reply.EncodedData, &recoveredData)
	if err != nil {
		return fmt.Errorf("failed to unmarshal recovered data: %v", err)
	}

	w.kVStore = recoveredData
	err = w.saveToFile()
	if err != nil {
		return fmt.Errorf("failed to save the recovered data %v", err)
	}

	return nil
}
