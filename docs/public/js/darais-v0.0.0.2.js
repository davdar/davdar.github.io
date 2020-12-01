//////////////////////
// DOM Manipulation //
//////////////////////

// Title

var title = $('meta[name=title]').attr('content');
$(document).attr('title',title);

// Nav

$('body').prepend($(
    " <nav class='navbar navbar-expand-md navbar-dark bg-dark mb-4'> "
  + "   <div class='container'>                                      "
  + "     <a id='nav-title' class='navbar-brand' href='#'>           "
  + "     </a>                                                       "
  + "   </div>                                                       "
  + " </nav>                                                         "
  ));
$('#nav-title').text(title);

// Main Styling

$('main')
  .addClass('container')
  .addClass('text-justify');

$('main').append($(
  " <div id='timestamp'></div> "
));

///////////////
// SCRIPTING //
///////////////

// Trigger Showdown
var sdown = new showdown.Converter();
sdown.setOption('tables', true);
sdown.setOption('disableForced4SpacesIndentedSublists', true);
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
