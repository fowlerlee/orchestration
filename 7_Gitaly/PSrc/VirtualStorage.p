type tReadReq = (source: machine, key: int) -> (value: seq[byte]);
type tWriteReq = (source: machine, key: int, value: seq[byte]) -> ();
type tReplicateReq = (source: machine, key: int, value: seq[byte]) -> ();


event eReadReq: tReadReq -> (value: seq[byte]);
event eWriteReq: tWriteReq -> ();
event eReadResp: tReadReq -> (value: seq[byte]);
event eWriteResp: tWriteReq -> ();
event eReplicateReq: tReplicateReq -> ();

machine VirtualStorage
{
  // data: map from account-id to data
  var data: map[int, seq[byte]];
  start state Init {
    entry (init_data: map[int, seq[byte]])
    {
      data = init_data;

      on eReadReq do (req: tReadReq) {
        assert req.accountId in data, "Invalid accountId received in the read request!";
        send req.source, eReadResp, (key = req.key, value = data[req.key]);
      }

      on eWriteReq do (req: tWriteReq) {
        data[req.key] = req.value;
        send req.source, eWriteResp;
      }
    }

    state WaitForReadRequests {
      on eReadReq do (req: tReadReq) {
        assert req.key in data, "Invalid key received in the read request!";
        send req.source, eReadResp, (data = data[req.key]);
      }
    }

    state WaitForWriteRequests {
      on eWriteReq do (req: tWriteReq) {
        data[req.key] = req.value;
        send req.source, eWriteResp, (key = req.key);
      }
    }

    state ReplicateStorage {
      on eReplicateReq do (req: tReplicateReq) {
        if (req.key in data) {
          send req.source, eReplicateResp, (key = req.key, value = data[req.key]);
        }
      }
    }
  }
}