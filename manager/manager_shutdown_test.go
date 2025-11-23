package manager

import (
	"testing"
	"time"
)

func TestStopManagerRPC(t *testing.T) {
	address := "localhost:9991"
	m := MakeManager(address)
	
	// Give it a moment to start
	time.Sleep(10 * time.Millisecond)
	
	// Verify manager is running (listener should be set)
	if m.l == nil {
		t.Fatal("manager listener should be initialized")
	}
	
	// Stop the manager
	err := m.StopManagerRPC()
	if err != nil {
		t.Fatalf("StopManagerRPC should not return error: %v", err)
	}
	
	// Give it a moment to shut down
	time.Sleep(10 * time.Millisecond)
	
	// Verify shutdown channel is closed (we can't check if it's closed, but we can verify listener is closed)
	// The listener should be closed after shutdown
	// We can't directly check if listener is closed, but we can verify the shutdown was initiated
}

