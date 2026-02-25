#let desmo(..items) = {
  set table(
    columns: (auto, auto),
    
    fill: (x, _) => 
      if x == 0 { rgb("eeeeee") },
    align: left,
    stroke: (x, _) => (
      top: 0.1pt,
      bottom: 0.1pt,
      left: if x != 1 { 0.1pt },
      right: if x != 0 { 0.1pt }
    )
  );

  let formatId(id) = box(
    inset: (right: 1em),
    text(
    size: 0.6em,
    font: "Arial",
    fill: rgb("0008"), 
    [#id]
  ));

  let formatContent(content) = box(
    inset: (top: .8em, left: 0.5em, right: 3em, bottom: .9em),
    content
  );


  align(center, 
    table( 
      ..items.pos()
      .enumerate()
      .map(((i, content)) => (formatId(i + 1), formatContent(content)))
      .flatten()
    )
  )
}
