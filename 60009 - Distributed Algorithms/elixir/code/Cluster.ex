defmodule Cluster do
  def start do
    # Spawn two processes, with the function start
    # Server.ex and Client.ex are modules containing a public start function
    # Here we just use the current node, we could specify other nodes
    n = Node.self()
    s = Node.spawn(n, Server, :start, [])
    c = Node.spawn(n, Client, :start, [])

    # We send the PIDs of the processes to each other
    send s, { :bind, c }
    send c, { :bind, s }
  end
end
