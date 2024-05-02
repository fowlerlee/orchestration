build:
	@go build -o bin/orchestration

run: build
	@./bin/orchestration

test:
	@go test -v ./...