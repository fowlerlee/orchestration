package gitaly

import (
	"fmt"
	"io"
	"net"
	"net/rpc"
	"os"
	"path/filepath"
	"sync"
	"time"

	"log"

	"github.com/fowlerlee/orchestration/common"
	"github.com/go-git/go-git/v5"
	"github.com/go-git/go-git/v5/plumbing"
	"github.com/go-git/go-git/v5/plumbing/filemode"
	"github.com/go-git/go-git/v5/plumbing/object"
	"github.com/go-git/go-git/v5/storage/filesystem"
	"github.com/google/uuid"
)

type GitalyWorker struct {
	ID      string
	Address string
	Repo    *git.Repository
}

type Gitaly struct {
	sync.Mutex
	Address     string
	Listener    net.Listener
	Shutdown    chan struct{}
	Gitter      *git.Repository
	Workers     []*GitalyWorker
	RepoPath    string
	NodeID      string
	storageFile string
}

func CreateGitaly(address string, repoPath string) (*Gitaly, error) {
	
	gitaly := &Gitaly{
		Address:  address,
		Listener: nil,
		Shutdown: make(chan struct{}),
		Workers:  make([]*GitalyWorker, 0),
		RepoPath: repoPath,
		NodeID:   uuid.New().String(),
		storageFile:  filepath.Join(repoPath, fmt.Sprintf("gitaly_%s_store.json", address)),
	}

	if _, err := os.Stat(repoPath); os.IsNotExist(err) {
		var err error
		gitaly.Gitter, err = git.PlainInit(repoPath, false)
		if err != nil {
			return nil, fmt.Errorf("failed to initialize git repository: %w", err)
		}
	} else {
		var err error
		gitaly.Gitter, err = git.PlainOpen(repoPath)
		if err != nil {
			return nil, fmt.Errorf("failed to open git repository: %w", err)
		}
	}

	return gitaly, nil
}

func (g *Gitaly) StartGitalyRPC() {
	rpcs := rpc.NewServer()
	errX := rpcs.Register(g)
	if errX != nil {
		log.Fatalf("failed to register gitaly with rpc server: %v", errX)
	}
	os.Remove(g.Address)
	l, err := net.Listen(common.Protocol, g.Address)
	if err != nil {
		log.Fatalf("gitaly RPC server not initiated: %v", err)
	}
	g.Listener = l
	fmt.Println("gitaly rpc seems to be live!")

	go func() {
	loop:
		for {
			select {
			case <-g.Shutdown:
				break loop
			default:
			}
			conn, err := g.Listener.Accept()
			if err == nil {
				go func() {
					rpcs.ServeConn(conn)
					conn.Close()
				}()
			} else {
				fmt.Printf("error accepting request from client, %v", err)
			}
			fmt.Println("worker successfully handled RPC call")
		}
	}()
}

func (g *Gitaly) AddWorker(args *common.GitalyAddWorkerArgs, reply *common.GitalyAddWorkerReply) error {
	g.Lock()
	defer g.Unlock()
	workerRepo, err := git.PlainOpen(args.RepoPath)
	if err != nil {
		reply.Success = false
		reply.Error = fmt.Sprintf("failed to open worker repository: %v", err)
		return err
	}

	gWorker := &GitalyWorker{
		ID:      args.WorkerID,
		Address: args.Address,
		Repo:    workerRepo,
	}

	g.Workers = append(g.Workers, gWorker)
	reply.Success = true
	return nil
}

// GetBlob retrieves a blob object from the git repository
func (g *Gitaly) GetBlob(args *common.GitalyGetBlobArgs, reply *common.GitalyGetBlobReply) error {
	g.Lock()
	defer g.Unlock()

	hash := plumbing.NewHash(args.ObjectID)
	if hash.IsZero() {
		reply.Success = false
		reply.Error = "invalid object ID"
		return fmt.Errorf("invalid object ID: %s", args.ObjectID)
	}

	obj, err := g.Gitter.Object(plumbing.AnyObject, hash)
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	blob, ok := obj.(*object.Blob)
	if !ok {
		reply.Success = false
		reply.Error = "object is not a blob"
		return fmt.Errorf("object %s is not a blob", args.ObjectID)
	}

	reader, err := blob.Reader()
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}
	defer reader.Close()

	content, err := io.ReadAll(reader)
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	reply.Content = content
	reply.Size = blob.Size
	reply.Success = true
	return nil
}

// WriteBlob writes a blob object to the git repository
func (g *Gitaly) WriteBlob(args *common.GitalyWriteBlobArgs, reply *common.GitalyWriteBlobReply) error {
	g.Lock()
	defer g.Unlock()

	// Get the storage
	storage := g.Gitter.Storer

	// Create memory object for blob
	obj := &plumbing.MemoryObject{}
	obj.SetType(plumbing.BlobObject)
	obj.SetSize(int64(len(args.Content)))

	// Write content to the object
	writer, err := obj.Writer()
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}
	if _, err := writer.Write(args.Content); err != nil {
		writer.Close()
		reply.Success = false
		reply.Error = err.Error()
		return err
	}
	writer.Close()

	// Write blob to storage
	hash, err := storage.SetEncodedObject(obj)
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	reply.ObjectID = hash.String()
	reply.Success = true
	return nil
}

// GetTree retrieves a tree object from the git repository
func (g *Gitaly) GetTree(args *common.GitalyGetTreeArgs, reply *common.GitalyGetTreeReply) error {
	g.Lock()
	defer g.Unlock()

	hash := plumbing.NewHash(args.TreeID)
	if hash.IsZero() {
		reply.Success = false
		reply.Error = "invalid tree ID"
		return fmt.Errorf("invalid tree ID: %s", args.TreeID)
	}

	obj, err := g.Gitter.Object(plumbing.TreeObject, hash)
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	tree, ok := obj.(*object.Tree)
	if !ok {
		reply.Success = false
		reply.Error = "object is not a tree"
		return fmt.Errorf("object %s is not a tree", args.TreeID)
	}

	entries := make([]common.TreeEntry, 0)

	var walkFunc func(*object.Tree, string) error
	walkFunc = func(t *object.Tree, path string) error {
		for _, entry := range t.Entries {
			fullPath := filepath.Join(path, entry.Name)
			treeEntry := common.TreeEntry{
				Name: fullPath,
				Mode: entry.Mode.String(),
				Hash: entry.Hash.String(),
			}

			switch entry.Mode {
			case filemode.Regular, filemode.Executable:
				treeEntry.Type = "blob"
			case filemode.Dir:
				treeEntry.Type = "tree"
				if args.Recursive {
					subTree, err := g.Gitter.TreeObject(entry.Hash)
					if err == nil {
						walkFunc(subTree, fullPath)
					}
				}
			}

			entries = append(entries, treeEntry)
		}
		return nil
	}

	if err := walkFunc(tree, ""); err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	reply.Entries = entries
	reply.Success = true
	return nil
}

// CreateTree creates a new tree object in the git repository
func (g *Gitaly) CreateTree(args *common.GitalyCreateTreeArgs, reply *common.GitalyCreateTreeReply) error {
	g.Lock()
	defer g.Unlock()

	storage := g.Gitter.Storer.(*filesystem.Storage)

	// Start with base tree if provided
	var baseTree *object.Tree
	if args.BaseTreeID != "" {
		hash := plumbing.NewHash(args.BaseTreeID)
		if !hash.IsZero() {
			obj, err := g.Gitter.Object(plumbing.TreeObject, hash)
			if err == nil {
				baseTree = obj.(*object.Tree)
			}
		}
	}

	// Create new tree
	tree := &object.Tree{}

	// Copy entries from base tree if exists
	if baseTree != nil {
		for _, entry := range baseTree.Entries {
			tree.Entries = append(tree.Entries, entry)
		}
	}

	// Add/update entries
	for _, entry := range args.Entries {
		hash := plumbing.NewHash(entry.Hash)
		mode, err := parseMode(entry.Mode)
		if err != nil {
			reply.Success = false
			reply.Error = fmt.Sprintf("invalid mode for %s: %v", entry.Name, err)
			return err
		}

		// Remove existing entry with same name if exists
		for i, e := range tree.Entries {
			if e.Name == entry.Name {
				tree.Entries = append(tree.Entries[:i], tree.Entries[i+1:]...)
				break
			}
		}

		tree.Entries = append(tree.Entries, object.TreeEntry{
			Name: entry.Name,
			Mode: mode,
			Hash: hash,
		})
	}

	// Write tree to storage
	obj := &plumbing.MemoryObject{}
	if err := tree.Encode(obj); err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	hash, err := storage.SetEncodedObject(obj)
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	reply.TreeID = hash.String()
	reply.Success = true
	return nil
}

// GetCommit retrieves a commit object from the git repository
func (g *Gitaly) GetCommit(args *common.GitalyGetCommitArgs, reply *common.GitalyGetCommitReply) error {
	g.Lock()
	defer g.Unlock()

	var hash plumbing.Hash
	var err error

	// Try to resolve as ref first
	ref, err := g.Gitter.Reference(plumbing.ReferenceName(args.CommitID), true)
	if err == nil {
		hash = ref.Hash()
	} else {
		// Try as direct hash
		hash = plumbing.NewHash(args.CommitID)
		if hash.IsZero() {
			reply.Success = false
			reply.Error = "invalid commit ID or ref"
			return fmt.Errorf("invalid commit ID: %s", args.CommitID)
		}
	}

	commit, err := g.Gitter.CommitObject(hash)
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	reply.CommitID = commit.Hash.String()
	reply.TreeID = commit.TreeHash.String()
	reply.ParentIDs = make([]string, 0)
	parentIter := commit.Parents()
	parentIter.ForEach(func(parent *object.Commit) error {
		reply.ParentIDs = append(reply.ParentIDs, parent.Hash.String())
		return nil
	})
	reply.Author = common.Signature{
		Name:  commit.Author.Name,
		Email: commit.Author.Email,
		When:  commit.Author.When.Format("2006-01-02T15:04:05Z07:00"),
	}
	reply.Committer = common.Signature{
		Name:  commit.Committer.Name,
		Email: commit.Committer.Email,
		When:  commit.Committer.When.Format("2006-01-02T15:04:05Z07:00"),
	}
	reply.Message = commit.Message
	reply.Success = true
	return nil
}

// CreateCommit creates a new commit object in the git repository
func (g *Gitaly) CreateCommit(args *common.GitalyCreateCommitArgs, reply *common.GitalyCreateCommitReply) error {
	g.Lock()
	defer g.Unlock()

	treeHash := plumbing.NewHash(args.TreeID)
	if treeHash.IsZero() {
		reply.Success = false
		reply.Error = "invalid tree ID"
		return fmt.Errorf("invalid tree ID: %s", args.TreeID)
	}

	// Parse parent commits
	parentHashes := make([]plumbing.Hash, 0, len(args.ParentIDs))
	for _, parentID := range args.ParentIDs {
		hash := plumbing.NewHash(parentID)
		if !hash.IsZero() {
			parentHashes = append(parentHashes, hash)
		}
	}

	// Parse signatures (use current time if parsing fails)
	authorWhen, err := time.Parse("2006-01-02T15:04:05Z07:00", args.Author.When)
	if err != nil {
		authorWhen = time.Now()
	}
	committerWhen, err := time.Parse("2006-01-02T15:04:05Z07:00", args.Committer.When)
	if err != nil {
		committerWhen = time.Now()
	}

	author := object.Signature{
		Name:  args.Author.Name,
		Email: args.Author.Email,
		When:  authorWhen,
	}

	committer := object.Signature{
		Name:  args.Committer.Name,
		Email: args.Committer.Email,
		When:  committerWhen,
	}

	// Create commit
	commit := &object.Commit{
		TreeHash:     treeHash,
		ParentHashes: parentHashes,
		Author:       author,
		Committer:    committer,
		Message:      args.Message,
	}

	// Write commit to storage
	storage := g.Gitter.Storer
	obj := &plumbing.MemoryObject{}
	if err := commit.Encode(obj); err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	hash, err := storage.SetEncodedObject(obj)
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	reply.CommitID = hash.String()
	reply.Success = true
	return nil
}

// GetRef retrieves a reference from the git repository
func (g *Gitaly) GetRef(args *common.GitalyGetRefArgs, reply *common.GitalyGetRefReply) error {
	g.Lock()
	defer g.Unlock()

	refName := plumbing.ReferenceName(args.RefName)
	ref, err := g.Gitter.Reference(refName, true)
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	reply.RefName = args.RefName
	reply.CommitID = ref.Hash().String()
	reply.Success = true
	return nil
}

// UpdateRef updates a reference in the git repository
func (g *Gitaly) UpdateRef(args *common.GitalyUpdateRefArgs, reply *common.GitalyUpdateRefReply) error {
	g.Lock()
	defer g.Unlock()

	refName := plumbing.ReferenceName(args.RefName)
	hash := plumbing.NewHash(args.CommitID)
	if hash.IsZero() {
		reply.Success = false
		reply.Error = "invalid commit ID"
		return fmt.Errorf("invalid commit ID: %s", args.CommitID)
	}

	newRef := plumbing.NewHashReference(refName, hash)

	// Check if ref exists
	_, err := g.Gitter.Reference(refName, false)
	if err == nil && !args.Force {
		// Ref exists and we're not forcing, so this is an error
		reply.Success = false
		reply.Error = "ref already exists (use Force=true to overwrite)"
		return fmt.Errorf("ref %s already exists", args.RefName)
	}

	if err := g.Gitter.Storer.SetReference(newRef); err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	reply.Success = true
	return nil
}

// ListRefs lists all references in the git repository
func (g *Gitaly) ListRefs(args *common.GitalyListRefsArgs, reply *common.GitalyListRefsReply) error {
	g.Lock()
	defer g.Unlock()

	refs, err := g.Gitter.References()
	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	refList := make([]common.RefInfo, 0)
	err = refs.ForEach(func(ref *plumbing.Reference) error {
		refName := ref.Name().String()

		// Apply pattern filter if provided
		if args.Pattern != "" {
			matched, _ := filepath.Match(args.Pattern, refName)
			if !matched {
				return nil
			}
		}

		refInfo := common.RefInfo{
			Name:     refName,
			CommitID: ref.Hash().String(),
		}

		// Determine ref type
		if ref.Name().IsBranch() {
			refInfo.Type = "branch"
		} else if ref.Name().IsTag() {
			refInfo.Type = "tag"
		} else {
			refInfo.Type = "other"
		}

		refList = append(refList, refInfo)
		return nil
	})

	if err != nil {
		reply.Success = false
		reply.Error = err.Error()
		return err
	}

	reply.Refs = refList
	reply.Success = true
	return nil
}

// Helper function to parse file mode string
func parseMode(modeStr string) (filemode.FileMode, error) {
	switch modeStr {
	case "100644", "644":
		return filemode.Regular, nil
	case "100755", "755":
		return filemode.Executable, nil
	case "040000", "40000":
		return filemode.Dir, nil
	case "120000":
		return filemode.Symlink, nil
	case "160000":
		return filemode.Submodule, nil
	default:
		// Try to parse as octal
		var mode int64
		_, err := fmt.Sscanf(modeStr, "%o", &mode)
		if err != nil {
			return 0, fmt.Errorf("invalid mode: %s", modeStr)
		}
		return filemode.FileMode(mode), nil
	}
}
