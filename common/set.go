package common

type Set[T comparable] struct {
	elements map[T]struct{}
}

func NewSet[T comparable]() *Set[T] {
	return &Set[T]{elements: make(map[T]struct{})}
}

func (s *Set[T]) Add(value T) {
	s.elements[value] = struct{}{}
}

func (s *Set[T]) Remove(value T) {
	delete(s.elements, value)
}

func (s *Set[T]) Contains(value T) bool {
	_, exists := s.elements[value]
	return exists
}

func (s *Set[T]) Size() int {
	return len(s.elements)
}

func (s *Set[T]) Values() []T {
	keys := make([]T, 0, len(s.elements))
	for k := range s.elements {
		keys = append(keys, k)
	}
	return keys
}
