

// Proxy module
module Proxy = { Proxy };

// Virtual Storage module
module VirtualStorage = { VirtualStorage };

// Cluster module
module Cluster = { Proxy, (virtualStorages: map[int, VirtualStorage]) };