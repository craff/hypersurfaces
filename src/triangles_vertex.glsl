precision highp float;
precision highp int;
uniform mat4 ModelView, Camera, Projection;
uniform vec4 lightDiffuse, lightAmbient, color;
uniform vec3 lightPos1, lightPos2, lightPos3;

in vec3  in_position, in_normal;

out vec4 diffuse, ambient, m_position;
out vec3 normal, halfVector1, halfVector2, halfVector3;

void main(){
  mat4 mcmv;

  // Pass the halfVector to the fragment shader.
  mcmv = Camera * ModelView;
  m_position = mcmv * vec4(in_position, 1.0);
  halfVector1 = normalize(lightPos1 - 2.0 * m_position.xyz);
  halfVector2 = normalize(lightPos2 - 2.0 * m_position.xyz);
  halfVector3 = normalize(lightPos3 - 2.0 * m_position.xyz);

  // Only works for orthogonal matrices.

  mat3 NormalMatrix =
    mat3(mcmv[0].xyz, mcmv[1].xyz, mcmv[2].xyz);

  // First transform the normal into eye space and normalize the result.
  normal = normalize(NormalMatrix * in_normal);
  if (dot(normal,m_position.xyz) > 0.0) normal = -normal;

  // Compute the diffuse, ambient and globalAmbient terms.
  diffuse = color * lightDiffuse;
  ambient = color * lightAmbient;
  gl_Position = Projection * m_position;
}
