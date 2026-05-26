package common

import (
	"fmt"
	"testing"
)

func TestCreatLSMTree(t *testing.T) {
	lsmtree := CreateTextLsmtree[Item[string]](5)
	lsmtree.addItem(&Item[string]{Name: "test1"})
	lsmtree.addItem(&Item[string]{Name: "test2"})
	lsmtree.addItem(&Item[string]{Name: "test3"})
	lsmtree.addItem(&Item[string]{Name: "test4"})
	lsmtree.addItem(&Item[string]{Name: "test5"})
	lsmtree.addItem(&Item[string]{Name: "test6"})
	lsmtree.addItem(&Item[string]{Name: "test7"})
	lsmtree.addItem(&Item[string]{Name: "test8"})
	lsmtree.addItem(&Item[string]{Name: "test9"})
	lsmtree.addItem(&Item[string]{Name: "test10"})
	lsmtree.addItem(&Item[string]{Name: "test11"})
	lsmtree.addItem(&Item[string]{Name: "test12"})
	lsmtree.addItem(&Item[string]{Name: "test13"})
	lsmtree.addItem(&Item[string]{Name: "test14"})
	lsmtree.addItem(&Item[string]{Name: "test15"})
	lsmtree.addItem(&Item[string]{Name: "test16"})
	lsmtree.addItem(&Item[string]{Name: "test17"})
	lsmtree.addItem(&Item[string]{Name: "test18"})
	lsmtree.addItem(&Item[string]{Name: "test19"})
	lsmtree.addItem(&Item[string]{Name: "test20"})

	fmt.Println(lsmtree.getLeftItem())
	fmt.Println(lsmtree.getRightItem())
	fmt.Println(lsmtree.getParentItem())

}
