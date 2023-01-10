defmodule Client do
  def start do
    receive do
      { :bind, s } -> next(s)
    end
  end

  defp next(s) do
    send s, { :circle, 1.0 }
    receive do
      { :result, area } -> IO.puts "Area is #{area}"
    end
    Process.sleep(1000)
    next(s)
  end
end
