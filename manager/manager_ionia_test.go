package manager



import (
	"fmt"
	"testing"
)

func TestIoniaClient(t *testing.T) {
	fmt.Println("testing")

	 n := NewIoniaNode()
	n.ListenForClient()
}