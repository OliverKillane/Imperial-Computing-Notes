# Broadcast using perfect point-to-point links
# processes <- the list of processes in the broadcast space
# pl        <- the perfect links process to use
# c         <- the object broadcasting & being delivered
defmodule Best_Effort_Broadcast do
  def start(processes) do
    receive do {:bind, pl, c} -> next(processes, pl, c)
  end

  defp next(processes, pl, c) do
    receive do
      {:beb_broadcast, msg} ->
        for dest <- processes do
          send pl, {:pl_send, dest, msg}
        end
      {:pl_deliver, src, msg} ->
        send c, {:beb_deliver, src, msg}
    end
    next (processes, pl, c)
  end
end
