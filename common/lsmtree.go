package common

type Item[T any] struct {
	isRoot     bool
	Name       string
	LeftItem   *Item[T]
	RightItem  *Item[T]
	ParentItem *Item[T]
	Capacity   int
}

func (t *Item[T]) addItem(node *T) {
	if t.isRoot {
		if t.LeftItem == nil && t.LeftItem.Capacity > len(t.getLeftItem()) {
			t.LeftItem = &Item[T]{Capacity: t.Capacity}
		}
		if t.RightItem == nil {
			t.RightItem = &Item[T]{Capacity: t.Capacity}
		}
		if t.ParentItem == nil {
			t.ParentItem = &Item[T]{Capacity: t.Capacity}
		}
		if len(t.getLeftItem()) < t.Capacity {
			t.LeftItem.addItem(node)
		} else if len(t.getRightItem()) < t.Capacity {
			t.RightItem.addItem(node)
		} else {
			t.LeftItem.addItem(node)
		}
	}
}

func (t *Item[T]) removeItem(node *T) {
	if t.LeftItem == nil {
		t.LeftItem = nil
		t.RightItem = nil
	} else {
		t.RightItem = nil
		t.ParentItem = nil
	}
}

func (t *Item[T]) getLeftItem() *Item[T] {
	return t.LeftItem
}

func (t *Item[T]) getRightItem() *Item[T] {
	return t.RightItem
}

func (t *Item[T]) getParentItem() *Item[T] {
	return t.ParentItem
}

func CreateLsmtree[T any](capacity int) *Item[T] {
	return &Item[T]{
		Capacity: capacity,
	}
}
