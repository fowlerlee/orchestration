package common

const ChunkSize = 1024

type BackupDataArgs struct {
	WorkerID    string
	EncodedData [][]byte
}

type BackupDataReply struct {
	Success bool
	EncodedData []byte
}

func EncodeXOR(data []byte) ([][]byte, error) {
	chunks := len(data) / ChunkSize
	if len(data)%ChunkSize != 0 {
		chunks++
	}

	encoded := make([][]byte, chunks+1)
	for i := 0; i < chunks; i++ {
		start := i * ChunkSize
		end := start + ChunkSize
		if end > len(data) {
			end = len(data)
		}
		encoded[i] = make([]byte, ChunkSize)
		copy(encoded[i], data[start:end])
	}

	encoded[chunks] = make([]byte, ChunkSize)
	for i := 0; i < chunks; i++ {
		for j := 0; j < ChunkSize; j++ {
			encoded[chunks][j] ^= encoded[i][j]
		}
	}
	return encoded, nil
}

func DecodeXOR(encoded [][]byte) ([]byte, error) {
	chunks := len(encoded) - 1
	data := make([]byte, chunks*ChunkSize)

	for i := 0; i < chunks; i++ {
		copy(data[i*ChunkSize:], encoded[i])
	}
	return data[:], nil
}
