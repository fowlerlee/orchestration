type tRedirectReq = (source: machine) -> (virtualStorage: VirtualStorage);
type tRedirectResp = (source: machine, virtualStorage: VirtualStorage);

event eRedirectReq: tRedirectReq;
event eRedirectResp: tRedirectResp;

machine Proxy {
  var virtualStorages: map[int, VirtualStorage];
  start state Init {
    entry {
      goto WaitForRedirectRequests;
    }

    on eRedirectReq do (req: tRedirectReq) {
      send req.source, eRedirectResp, (virtualStorage = virtualStorages[req.source]);
    }

    state WaitForRedirectRequests {
      on eRedirectReq do (req: tRedirectReq) {
        if (req.source in virtualStorages) {
          virtualStorages[req.source] = req.virtualStorage;
        } else {
          virtualStorages += (req.source, req.virtualStorage);
        }
        send req.source, eRedirectResp;
      }
    }
    state WaitForRedirectResponses {
      on eRedirectResp do (resp: tRedirectResp) {
        send resp.source, eRedirectReq, (virtualStorage = resp.virtualStorage);
      }
    }
    state WaitForStorageRequests {
      on eStorageReq do (req: tStorageReq) {
        send req.source, eStorageResp, (value = req.value) -> (virtualStorage = virtualStorages[req.source]);
      }
    }
    state WaitForStorageResponses {
      on eStorageResp do (resp: tStorageResp) {
        send resp.source, eStorageReq, (virtualStorage = resp.virtualStorage);
      }
    }
    state WaitForProxyRequests {
      on eProxyReq do (req: tProxyReq) {
        send req.source, eProxyResp, (virtualStorage = virtualStorages[req.source]);
      }
    }
    state WaitForProxyResponses {
      on eProxyResp do (resp: tProxyResp) {
        send resp.source, eProxyReq, (virtualStorage = resp.virtualStorage);
      }
    }
  }
}