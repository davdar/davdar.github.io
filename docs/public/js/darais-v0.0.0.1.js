// Trigger Showdown
var sdown = new showdown.Converter();
sdown.setOption('tables', true);
$("pre.markdown").each(function () {
  var e = $("<div class=markdown></div>");
  e.html(sdown.makeHtml($(this).text()));
  $.each(this.attributes,function(i,a) {
    e.attr(a.name,a.value);
  });
  $(this).replaceWith(e);
});

// Tables
$("table").each(function () {
  $(this).addClass("table table-striped table-borderless table-sm");
});
$("thead").each(function () {
  $(this).addClass("thead-dark");
});

// Lists
$("li p").contents().unwrap();

// Timestamp
$("#timestamp")
  .addClass("text-right")
  .addClass("text-secondary")
  .append($("<em>Last updated: " + new Date(document.lastModified).toLocaleDateString() + "</em>"));
