package manager


import "fmt"


type IoniaNode struct {
	IoniaManager Manager 

}

func (i *IoniaNode) ListenForClient()  {
	var address = i.IoniaManager.address
	fmt.Printf("Address: %s", address)
	i.IoniaManager.StartManagerRPC()

	i.IoniaManager.BecomeLeader()
	
}


func NewIoniaNode() *IoniaNode {
	fmt.Println("creating an ionia node")
	return &IoniaNode{}
}

