package worker

import (
	
	"testing"
	"github.com/stretchr/testify/assert"
)

func TestGaloisAssociative(t *testing.T) {
	g := CreateGalois()
	for i := -128; i < 128; i++ {
		a := int8(i)
		for j := -128; j < 128; j++ {
			b := int8(j)
			for k := 0; k < 128; k++ {
				c := int8(k)
				assert.Equal(t, g.add(a, g.add(b, c)), g.add(g.add(a, b), c))
				assert.Equal(t, g.multiply(a, g.multiply(b, c)), g.multiply(g.multiply(a, b), c))
			}
		}
	}
}

func TestIdentity(t *testing.T) {
	g := CreateGalois()
	for i := -128; i < 128; i++ {
		a := int8(i)
		assert.Equal(t, a, g.add(a, int8(0)))
		assert.Equal(t, a, g.multiply(a, int8(1)))
	}
}

func TestGaloisCommutative(t *testing.T) {
	g := CreateGalois()
	for i := -128; i < 128; i++ {
		for j := -128; j < 128; j++ {
			a := int8(i)
			b := int8(j)
			assert.Equal(t, g.add(a, b), g.add(b, a))
			assert.Equal(t, g.multiply(a, b), g.multiply(b, a))
		}
	}
}


