package gitaly

import (
	"fmt"
	"testing"
	"os"
	"time"

)


func TestGitaly(t *testing.T) {
	fmt.Println("testing gitaly")
	filepath := os.TempDir() + "/gitaly"
	address := "localhost:8080"
	var gitaly *Gitaly
	var err error
	if gitaly, err = CreateGitaly(address, filepath); err != nil {
		t.Fatalf("failed to create a gitaly instance: %v", err)
	}
	gitaly.StartGitalyRPC()
	time.Sleep(1 * time.Second)




	gitaly.Shutdown <- struct{}{}

}