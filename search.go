package main

import (
	"fmt"
	"sync"
)

func One() {
	fmt.Println("hello one")
}

type BinarySearchTree struct {
	tree []TreeNode
}

type Color int

const (
	Red   Color = 0
	Black Color = 1
)

type TreeNode struct {
	key   int
	value string
	color Color
}

type TreeSet struct {
	bst *BinarySearchTree
}

func (treeSet *TreeSet) InsertTreeNode(treeNodes ...TreeNode) {
	var treeNode TreeNode
	for _, treeNode = range treeNodes {
		treeSet.bst.InsertElement(treeNode.key, treeNode.value, treeNode.color)
	}
}

func (bst *BinarySearchTree) InsertElement(key int, value string, color Color) {
	bst.tree = append(bst.tree, TreeNode{key, value, color})
}

func (bst *BinarySearchTree) InOrderTraverseTree() {
	var l sync.Locker
	l.Lock()
	defer l.Unlock()
	for len(bst.tree) > 0 {
		for _, v := range bst.tree {
			var s []TreeNode
			v.color = Color(1)
			s = append(s, v)
					

		}
	}
}
