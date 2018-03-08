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
            set output_source "Typechecking ...";
            input <- get input_source;
            output <- rpc (do_process input);
            
            (* let *)
            (*     (\* val output = do_process input *\) *)
            (*     val output = "" *)
            (* in *)
                set output_source output
            (* end *)
    in
        return <xml>
          <head>
            <title>Example TiML Programs</title>
          </head>
          <body>
          <h1>{["TiML - A Functional Language with Static Time Complexity Guarantees"]}</h1>
          (* <h2>{["by Peng Wang <wangpeng@csail.mit.edu>"]}</h2> *)
          <h2>{["by "]}<a href="https://people.csail.mit.edu/wangpeng/">Peng Wang</a>{[" <wangpeng at csail dot mit dot edu>"]}</h2>
          <hr/>
          <a href="/examples.html">Example TiML Programs</a><br/>
          <hr/>
          <br/>
          <ctextarea rows=40 cols=160 source={input_source}/>
          <br/>
          <button value="Typecheck" onclick={fn _ => process ()}/><br/>
          <br/>

          <dyn signal={show output_source}/>
          </body>
          </xml>
    end
