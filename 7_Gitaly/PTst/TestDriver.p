
// Test driver that checks the system with a single Client.
machine TestWithSingleClient
{
  start state Init {
    entry {
      SetupProxySystem(1);
    }
  }
}

// Test driver that checks the system with multiple Clients.
machine TestWithMultipleClients
{
  start state Init {
    entry {
      // multiple clients between (2, 4)
      SetupProxySystem(choose(3) + 2);
    }
  }
}

param nClients: int;

machine TestWithConfig {
  start state Init {
    entry {
      SetupProxySystem(nClients);
    }
  }
}

// creates a random map from accountId's to account balance of size `numAccounts`
fun CreateRandomInitialAccounts(numAccounts: int) : map[int, int]
{
  var i: int;
  var bankBalance: map[int, int];
  while(i < numAccounts) {
    bankBalance[i] = choose(100) + 10; // min 10 in the account
/* Hint 1: Reduce the number of choices by changing the above line to the following:
    // bankBalance[i] = choose(10) + 10; // min 10 in the account
*/
    i = i + 1;
  }
  return bankBalance;
}

// setup the client server system with one bank server and `numClients` clients.
fun SetupProxySystem(numClients: int)
{
  var i: int;
  var proxy: Proxy;
  var virtualStorages: map[int, VirtualStorage];
  var cluster: Cluster;

  // create the virtual storages
  while(i < numClients) {
    virtualStorages += (i, new VirtualStorage(CreateRandomInitialAccounts(numClients)));
    i = i + 1;
  }

  // create the proxy
  proxy = new Proxy();

  // create the cluster
  cluster = new Cluster((proxy = proxy, virtualStorages = virtualStorages));
}