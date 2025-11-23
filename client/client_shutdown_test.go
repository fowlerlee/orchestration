package client

import (
	"testing"
	"time"
)

func TestStopClientRPC(t *testing.T) {
	address := "localhost:9992"
	c := MakeClient(address)
	c.StartClientRPC()
	
	// Give it a moment to start
	time.Sleep(10 * time.Millisecond)
	
	// Verify client is running (listener should be set)
	if c.l == nil {
		t.Fatal("client listener should be initialized")
	}
	
	// Stop the client
	err := c.StopClientRPC()
	if err != nil {
		t.Fatalf("StopClientRPC should not return error: %v", err)
	}
	
	// Give it a moment to shut down
	time.Sleep(100 * time.Millisecond)

	// Verify listener is closed
	if c.l != nil {
		t.Fatal("client listener should be closed after shutdown")
	}

	// Verify shutdown channel is closed
	if c.shutdown != nil {
		t.Fatal("client shutdown channel should be closed after shutdown")
	}

	// Verify shutdown complete is true
	if !c.shutdownComplete {
		t.Fatal("client shutdown complete should be true after shutdown")
	}
}

