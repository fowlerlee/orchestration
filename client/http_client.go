package client

import (
	"fmt"
	"net/http"
)

func addHttpEndPointHandlers(c *Client) {
	http.HandleFunc("/health", c.healthCheckHandler)
	http.HandleFunc("/kill", c.killServerHandler)
	// c.wg.Add(1)
	go func() {
		if err := c.httpServer.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			fmt.Printf("HTTP server error: %v\n", err)
		}
	}()
}

func (c *Client) healthCheckHandler(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}
	select {
	case <-c.shutdown:
		http.Error(w, "client server is not working", http.StatusInternalServerError)
	default:
		w.WriteHeader(http.StatusOK)
		w.Write([]byte("client server is up and running"))
	}
}

func (c *Client) killServerHandler(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "method not allowed", http.StatusMethodNotAllowed)
		return
	}
	w.WriteHeader(http.StatusOK)
	w.Write([]byte("Client server shutdown initiated"))

	go func() {
		if err := c.StopClientRPC(); err != nil {
			fmt.Printf("Error stopping client RPC: %v\n", err)
		}
	}()

}
