build:
	@go build -o bin/orchestration

run: build
	@./bin/orchestration

test:
	@go test -v ./...

# GeeqoDB targets
setup-geeqodb:
	@chmod +x scripts/setup_geeqodb.sh
	@./scripts/setup_geeqodb.sh

setup-geeqodb-download:
	@chmod +x scripts/setup_geeqodb.sh
	@./scripts/setup_geeqodb.sh --download-only

setup-geeqodb-build:
	@chmod +x scripts/setup_geeqodb.sh
	@./scripts/setup_geeqodb.sh --build-only

setup-geeqodb-clean:
	@chmod +x scripts/setup_geeqodb.sh
	@./scripts/setup_geeqodb.sh --clean

test-geeqodb-setup:
	@chmod +x scripts/setup_geeqodb_test.sh
	@./scripts/setup_geeqodb_test.sh

# Clean targets
clean:
	@rm -rf bin/
	@rm -rf database/
	@rm -rf geeqodb/

.PHONY: build run test setup-geeqodb setup-geeqodb-download setup-geeqodb-build setup-geeqodb-clean test-geeqodb-setup clean