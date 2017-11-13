fun do_process input =
let
    val output = Cmodule.doprocess input
    (* val output = Lib.important input *)
(* val output = "" *)
in
    return output
end


fun show ss =
    s <- signal ss;
    return <xml><pre>{[s]}</pre></xml>

fun main () =
    input_source <- source "";
    output_source <- source "";

    let
        fun process () =
            input <- get input_source;
            output <- rpc (do_process input);
            
            (* let *)
            (*     (\* val output = do_process input *\) *)
            (*     val output = "" *)
            (* in *)
                set output_source output
            (* end *)
    in
        return <xml><body>
          <h1>{["TiML"]}</h1>
          <hr/>
          <br/>
          <ctextarea source={input_source}/>
          <br/>
          <button value="Typecheck" onclick={fn _ => process ()}/><br/>
          <br/>

          <dyn signal={show output_source}/>
        </body></xml>
    end
