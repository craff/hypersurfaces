uniform mat4 ModelView, Camera, Projection;
uniform vec4 lightDiffuse, color;

in vec3 in_position;

out vec4 diffuse;

void main(){
  // Compute the diffuse, ambient and globalAmbient terms.
  diffuse = color * lightDiffuse;
  gl_Position = Projection * Camera * ModelView * vec4(in_position, 1.0);
}
