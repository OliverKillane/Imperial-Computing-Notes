defmodule Server do
  def start do
    receive do
      { :bind, c } -> next(c)
    end
 end

  defp next(c) do
    receive do
      { :circle, radius } ->
        send c, { :result, 3.14159 * radius * radius}
      { :square, side } ->
        send c, { :result, side * side}
    end
    next(c)
  end
end
