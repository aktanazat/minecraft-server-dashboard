#!/bin/zsh
ip=$(ipconfig getifaddr en0)
if [ -z "$ip" ]; then
  ip=$(ipconfig getifaddr en1)
fi
if [ -z "$ip" ]; then
  echo "No local IP found"
  exit 1
fi
echo "$ip:25565"
