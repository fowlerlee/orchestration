package worker

import (
	"reflect"
	"testing"
)

func TestGaloisAssociative(t *testing.T) {
	g1 := CreateGalois()
	g2 := CreateGalois()
	for i := -128; i < 128; i++ {
		a := int8(i)
		for j := -128; j < 128; j++ {
			b := int8(j)
			for k := 0; k < 128; k++ {
				c := int8(k)
				reflect.DeepEqual(g1.Add(a, g1.Add(b, c)),
					g2.Add(g2.Add(a, b), c))
			}
		}
	}
}
