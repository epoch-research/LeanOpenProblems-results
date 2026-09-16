import socket

def http_get(host, path):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.connect((host, 80))
    s.sendall(f"GET {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\n\r\n".encode())
    response = b""
    while True:
        data = s.recv(4096)
        if not data: break
        response += data
    return response.decode('utf-8', errors='ignore')

print(http_get("oeis.org", "/search?q=id:A046969&fmt=json"))
