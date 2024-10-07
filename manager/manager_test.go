package manager

// import (
// 	"bytes"
// 	"encoding/json"
// 	"fmt"
// 	"net/http"
// 	"net/http/httptest"
// 	"testing"
// 	// Replace with your handler package path
// )

// // Define a struct for your request body
// type submitRequest struct {
// 	Data string `json:"data"`
// }

// func TestSubmitHandler(t *testing.T) {
// 	// Prepare test data
// 	jsonData := []byte(`{"data": "This is some test data"}`)
// 	req, err := http.NewRequest("POST", "/submit", bytes.NewReader(jsonData))
// 	if err != nil {
// 		t.Fatal(err)
// 	}

// 	// Create a recorder to capture the response
// 	rr := httptest.NewRecorder()
// 	handler := http.HandlerFunc(handlers.SubmitHandler)

// 	// Call the handler
// 	handler.ServeHTTP(rr, req)

// 	// Check for expected status code
// 	if status := rr.Code; status != http.StatusOK {
// 		t.Errorf("handler returned wrong status code: got %v want %v", status, http.StatusOK)
// 	}

// 	// Optionally check response body (modify based on your expected response)
// 	var response map[string]string
// 	err = json.Unmarshal(rr.Body.Bytes(), &response)
// 	if err != nil {
// 		t.Errorf("failed to unmarshal response body: %v", err)
// 	}

// 	expected := map[string]string{"message": "Data received successfully"}
// 	if diff := compareMaps(response, expected); diff != "" {
// 		t.Errorf("Unexpected response body: %v", diff)
// 	}
// }

// // Helper function to compare maps (optional)
// func compareMaps(m1, m2 map[string]string) string {
// 	for k, v := range m1 {
// 		if m2[k] != v {
// 			return fmt.Sprintf("Key '%s': Mismatch. Expected: %s, Got: %s", k, v, m2[k])
// 		}
// 	}
// 	for k, v := range m2 {
// 		if _, ok := m1[k]; !ok {
// 			return fmt.Sprintf("Unexpected key '%s' in map 2", k)
// 		}
// 	}
// 	return ""
// }
